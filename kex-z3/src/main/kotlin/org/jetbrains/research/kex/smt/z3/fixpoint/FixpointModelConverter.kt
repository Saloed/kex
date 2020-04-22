package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.*
import com.microsoft.z3.enumerations.Z3_lbool
import org.jetbrains.research.kex.ktype.*
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.smt.z3.Z3Unlogic
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.*
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.util.join
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.ConcreteClass
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.ir.OuterClass
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.type.Type
import org.jetbrains.research.kfg.type.TypeFactory
import ru.spbstu.ktuples.zip

class FixpointModelConverter(
        private val mapping: ModelDeclarationMapping,
        private val tf: TypeFactory,
        private val z3Context: Z3Context
) {

    fun apply(expr: Expr): PredicateState = expr.simplify()
            .let { convert(it) }
            .let { InstanceOfCorrector(z3Context).apply(it) }
            .simplify()

    object UnknownType : KexType() {
        override val name: String = "Unknown"
        override val bitsize: Int = 0
        override fun getKfgType(types: TypeFactory): Type = throw IllegalStateException("type is unknown")
    }

    class InstanceOfCorrector(private val z3Context: Z3Context) : Transformer<InstanceOfCorrector> {
        class UnknownInstanceOfCollector : Transformer<UnknownInstanceOfCollector> {
            val predicatesToCorrect = arrayListOf<EqualityPredicate>()
            override fun transformEqualityPredicate(predicate: EqualityPredicate): Predicate {
                if (instanceOfPattern(predicate)) {
                    predicatesToCorrect.add(predicate)
                }
                return super.transformEqualityPredicate(predicate)
            }

            private fun instanceOfPattern(predicate: EqualityPredicate): Boolean {
                if (predicate.rhv !is ConstBoolTerm) return false
                val lhv = predicate.lhv as? CmpTerm ?: return false
                val instanceOf = lhv.lhv as? InstanceOfTerm ?: return false
                return instanceOf.checkedType is UnknownType
            }
        }

        override fun apply(ps: PredicateState): PredicateState {
            val unknownInstanceOf = UnknownInstanceOfCollector().apply { apply(ps) }.predicatesToCorrect
            if (unknownInstanceOf.isEmpty()) return ps
            val knownTypes = z3Context.getTypeMapping()
            val typeSets = unknownInstanceOf.map { findTypeSet(it) }
            val reifiedTypeSets = typeSets.map { it.reify(typeSets) }
            val typeCandidates = reifiedTypeSets.map { it.candidates(knownTypes) }
            val mapping = zip(reifiedTypeSets, typeCandidates, unknownInstanceOf)
                    .map { (ts, candi, originalPredicate) ->
                        originalPredicate to generateInstanceOf(ts, candi, originalPredicate)
                    }.toMap<Predicate, PredicateState>()
            return replaceWithPredicateState(ps, mapping)
        }

        private fun generateInstanceOf(typeSet: TypeSet, candidate: KexType, original: Predicate): PredicateState =
                predicate(original.type, original.location) {
                    InstanceOfTerm(candidate, typeSet.instanceOfArg) equality const(true)
                }.wrap()

        private fun generateInstanceOf(typeSet: TypeSet, candidates: Set<KexType>, original: Predicate): PredicateState = when (candidates.size) {
            0 -> throw IllegalStateException("No type candidates for $typeSet")
            1 -> generateInstanceOf(typeSet, candidates.first(), original)
            else -> candidates.map { generateInstanceOf(typeSet, it, original) }.let { ChoiceState(it) }
        }

        private fun replaceWithPredicateState(ps: PredicateState, replacement: Map<Predicate, PredicateState>): PredicateState = when (ps) {
            is BasicState -> when {
                ps.predicates.any { it in replacement }.not() -> ps
                else -> {
                    val builder = StateBuilder()
                    for (predicate in ps.predicates) {
                        when (val replaceWith = replacement[predicate]) {
                            null -> builder += predicate
                            else -> builder += replaceWith
                        }
                    }
                    builder.apply()
                }
            }
            else -> ps.fmap { replaceWithPredicateState(it, replacement) }
        }

        enum class TypeSearchDirection(val predicate: (Int, Int) -> Boolean) {
            EQ({ a, b -> a == b }),
            NEQ({ a, b -> a != b }),
            LT({ a, b -> a < b }),
            GT({ a, b -> a > b }),
            LE({ a, b -> a <= b }),
            GE({ a, b -> a >= b });

            fun invert() = when (this) {
                EQ -> NEQ
                NEQ -> EQ
                LT -> GE
                GT -> LE
                LE -> GT
                GE -> LT
            }

            companion object {
                fun from(opcode: CmpOpcode) = when (opcode) {
                    is CmpOpcode.Eq -> EQ
                    is CmpOpcode.Neq -> NEQ
                    is CmpOpcode.Lt -> LT
                    is CmpOpcode.Gt -> GT
                    is CmpOpcode.Le -> LE
                    is CmpOpcode.Ge -> GE
                    else -> TODO("Unexpected cmp opcode: $opcode")
                }
            }
        }

        data class TypeSet(val instanceOfArg: Term, val bound: Int, val direction: TypeSearchDirection) {
            fun candidates(types: Map<KexType, Int>) = types.entries
                    .filter { direction.predicate(it.value, bound) }
                    .map { it.key }
                    .toSet()

            private val needReification = bound % Z3Context.TYPE_IDX_MULTIPLIER != 0

            fun reify(typeSets: List<TypeSet>): TypeSet = when {
                !needReification -> this
                direction == TypeSearchDirection.EQ -> this
                direction == TypeSearchDirection.NEQ -> this
                else -> {
                    val myClosesIdx = closestPossibleIndex
                    val possibleReifications = typeSets.filter { it.closestPossibleIndex == myClosesIdx }
                    when (possibleReifications.size) {
                        1 -> TypeSet(instanceOfArg, myClosesIdx, TypeSearchDirection.EQ)
                        else -> this
                    }
                }
            }

            private val closestPossibleIndex by lazy {
                when {
                    !needReification -> bound
                    direction == TypeSearchDirection.LE || direction == TypeSearchDirection.LT -> {
                        (bound / Z3Context.TYPE_IDX_MULTIPLIER) * Z3Context.TYPE_IDX_MULTIPLIER
                    }
                    direction == TypeSearchDirection.GE || direction == TypeSearchDirection.GT -> {
                        (bound / Z3Context.TYPE_IDX_MULTIPLIER) * Z3Context.TYPE_IDX_MULTIPLIER + Z3Context.TYPE_IDX_MULTIPLIER
                    }
                    else -> throw IllegalArgumentException("No nearest index from $bound in direction $direction")
                }
            }
        }

        private fun findTypeSet(predicate: EqualityPredicate): TypeSet {
            val isTrue = (predicate.rhv as ConstBoolTerm).value
            val cmp = predicate.lhv as CmpTerm
            val bound = (cmp.rhv as ConstIntTerm).value
            val arg = (cmp.lhv as InstanceOfTerm).operand
            val direction = when {
                isTrue -> TypeSearchDirection.from(cmp.opcode)
                else -> TypeSearchDirection.from(cmp.opcode).invert()
            }
            return TypeSet(arg, bound, direction)
        }
    }

    private fun convert(expr: Expr): PredicateState = when (expr) {
        is BoolExpr -> convert(expr)
        else -> convertTerm(expr).equality { const(true) }
    }

    private fun convertTerm(expr: Expr): TermWithAxiom = when {
        expr.isVar -> convertVariableTerm(expr)
        expr.isSelect && expr.numArgs == 2 -> convertMemoryLoad(expr.args[0], expr.args[1])
        expr is BoolExpr -> convertBoolTerm(expr)
        expr is IntExpr -> convertIntTerm(expr)
        expr is BitVecExpr -> convertBVTerm(expr)
        expr is FPExpr -> convertFPTerm(expr)
        else -> TODO()
    }

    private fun convertVariableTerm(expr: Expr): TermWithAxiom =
            when (val term = mapping.getTerm(expr.index)) {
                is CallTerm -> {
                    val value = term { value(term.type, "call__${expr.index}") }
                    val axiom = basic {
                        state { value.call(term) }
                    }
                    TermWithAxiom(value, axiom)
                }
                else -> TermWithAxiom(term)
            }

    private fun convert(expr: BoolExpr): PredicateState = when {
        expr.isAnd -> expr.args.map { convert(it) }.combine { a, b -> ChainState(a, b) }.simplify()
        expr.isOr -> ChoiceState(expr.args.map { convert(it) }).simplify()
        expr.isNot && expr.numArgs == 1 -> convertTerm(expr.args.first()).equality { const(false) }
        expr.isEq && expr.numArgs == 2 -> {
            val (lhs, rhs) = expr.convertArgs()
            lhs.equality(rhs)
        }
        else -> convertTerm(expr).equality { const(true) }
    }

    private fun convertBoolTerm(expr: BoolExpr): TermWithAxiom = when {
        expr.isAnd -> expr.convertArgs().combine { a, b -> a and b }
        expr.isOr -> expr.convertArgs().combine { a, b -> a or b }
        expr.isNot && expr.numArgs == 1 -> expr.convertArgs().first().transformTerm { it.not() }
        expr.isEq && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a eq b }
        expr.isLE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a le b }
        expr.isGE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a ge b }
        expr.isConst && expr.boolValue == Z3_lbool.Z3_L_TRUE -> TermWithAxiom.wrap { const(true) }
        expr.isConst && expr.boolValue == Z3_lbool.Z3_L_FALSE -> TermWithAxiom.wrap { const(false) }
        expr.isBVSLE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a le b }
        expr.isBVSGE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a ge b }
        else -> TODO()
    }

    private fun convertIntTerm(expr: IntExpr): TermWithAxiom = when {
        expr.isIntNum -> TermWithAxiom.wrap {
            val intExpr = expr as IntNum
            val longValue = intExpr.int64
            when {
                longValue >= Int.MIN_VALUE.toLong() || longValue <= Int.MAX_VALUE.toLong() -> const(longValue.toInt())
                else -> const(longValue)
            }
        }
        expr.isAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isMul -> expr.convertArgs().combine { a, b -> a mul b }
        else -> TODO()
    }

    private fun convertBVTerm(expr: BitVecExpr): TermWithAxiom = when {
        expr is BitVecNum -> TermWithAxiom.wrap { Z3Unlogic.undo(expr) }
        expr.isBVAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isBVMul -> expr.convertArgs().combine { a, b -> a mul b }
        else -> TODO()
    }

    private fun convertFPTerm(expr: FPExpr): TermWithAxiom = when {
        expr is FPNum -> TermWithAxiom.wrap { Z3Unlogic.undo(expr) }
        else -> TODO()
    }

    private fun convertMemoryLoad(memory: Expr, location: Expr): TermWithAxiom {
        if (!memory.isVar) throw IllegalStateException("Memory is not var $memory")
        val decl = mapping.declarations[memory.index]
        return when {
            decl is DeclarationTracker.Declaration.Property -> readProperty(convertTerm(location), decl)
            decl is DeclarationTracker.Declaration.Memory && mapping.isArrayMemory(decl) -> {
                if (!(location.isAdd && location.args.size == 2)) {
                    throw IllegalStateException("Unexpected array memory location $location")
                }
                val (lhs, rhs) = location.convertArgs()
                val (base, index) = when {
                    lhs.term.type is KexArray -> lhs to rhs
                    rhs.term.type is KexArray -> rhs to lhs
                    else -> throw IllegalStateException("Array load has no base and index")
                }
                val arrayIndex = base.binaryOperation(index) { b, i -> tf.getArrayIndex(b, i) }
                arrayIndex.transformTerm { tf.getArrayLoad(it) }
            }
            else -> throw IllegalStateException("Unexpected memory $memory : $decl")
        }
    }

    private fun readProperty(obj: TermWithAxiom, property: DeclarationTracker.Declaration.Property): TermWithAxiom = when (property) {
        is DeclarationTracker.Declaration.ClassProperty -> {
            val kType = obj.term.type.getKfgType(tf)
            if (kType !is ClassType) {
                TODO("Only class types supported")
            }
            val fieldLoad = getFieldLoad(obj.term, tf.cm[property.className], property.propertyName)
            obj.binaryOperation(fieldLoad) { _, load -> load }
        }
        else -> when {
            property.fullName == Z3Context.TYPE_PROPERTY -> obj.transformTerm { InstanceOfTerm(UnknownType, it) }
            obj.term.type is KexArray && property.fullName == "length" -> obj.transformTerm { ArrayLengthTerm(KexInt(), it) }
            else -> TODO("Unknown property $property")
        }

    }

    private fun getFieldLoad(owner: Term, cls: Class, fieldName: String): TermWithAxiom {
        val field = cls.findField(fieldName)
        if (field != null) {
            return TermWithAxiom.wrap { owner.field(field.type.kexType, field.name).load() }
        }
        val fields = tf.cm.concreteClasses
                .filter { it.isInheritorOf(cls) }
                .mapNotNull { it.findField(fieldName) }
                .toSet()
        if (fields.isEmpty()) throw IllegalArgumentException("Class $cls and it inheritors has no field $fieldName")
        val fieldType = fields.map { it.type.kexType }.groupBy({ it }, { 1 }).maxBy { (_, cnt) -> cnt.sum() }?.key
                ?: throw IllegalStateException("No types")
        val resultFiledLoad = term { value(fieldType, "load_${cls.name}.$fieldName") }
        val axioms = fields.map {
            basic {
                path {
                    owner.instanceOf(it.`class`) equality const(true)
                }
                state {
                    resultFiledLoad equality tf.getCast(it.`class`.kexType, owner).field(it.type.kexType, it.name).load()
                }
            }
        }
        return TermWithAxiom(resultFiledLoad, ChoiceState(axioms))
    }

    private fun Term.instanceOf(cls: Class): Term = cls.allInheritors()
            .map { it.kexType }
            .map { term { tf.getInstanceOf(it, this@instanceOf) } }
            .join { t1, t2 -> term { t1 or t2 } }

    private fun Class.allInheritors() = cm.concreteClasses.filter { it.isInheritorOf(this) }.toSet()

    private data class TermWithAxiom(val term: Term, val axiom: PredicateState? = null) {

        fun equality(other: TermWithAxiom): PredicateState {
            val predicate = path { term equality other.term }
            val axiom = mergeAxiom(other)
            return withAxiom(predicate, axiom)
        }

        fun equality(builder: TermBuilder.() -> Term): PredicateState = equality(wrap(builder))

        fun binaryOperation(other: TermWithAxiom, operation: TermBuilder.(Term, Term) -> Term): TermWithAxiom =
                TermWithAxiom(TermBuilder.Terms.operation(term, other.term), mergeAxiom(other))

        fun transformTerm(operation: TermBuilder.(Term) -> Term) = copy(term = TermBuilder.Terms.operation(term))

        private fun withAxiom(predicate: Predicate, axiom: PredicateState?): PredicateState {
            val state = BasicState(listOf(predicate))
            return when {
                axiom != null -> ChainState(axiom, state)
                else -> state
            }
        }

        private fun mergeAxiom(other: TermWithAxiom) = when {
            axiom != null && other.axiom != null -> ChainState(axiom, other.axiom)
            else -> axiom ?: other.axiom
        }

        companion object {
            fun wrap(builder: TermBuilder.() -> Term) = TermWithAxiom(TermBuilder.Terms.builder())
        }
    }

    private fun Expr.convertArgs() = args.map { convertTerm(it) }
    private fun List<TermWithAxiom>.combine(combiner: TermBuilder.(Term, Term) -> Term): TermWithAxiom = when (size) {
        0, 1 -> throw  IllegalArgumentException("Nothing to combine")
        else -> drop(1).fold(first()) { acc, term -> acc.binaryOperation(term, combiner) }
    }

    private fun List<PredicateState>.combine(combiner: (PredicateState, PredicateState) -> PredicateState): PredicateState = when (size) {
        0 -> BasicState()
        else -> drop(1).fold(first(), combiner)
    }

    private fun Class.findFieldConcrete(name: String): Field? {
        return fields.find { it.name == name } ?: superClass?.findFieldConcrete(name)
    }

    private fun Class.findField(name: String): Field? {
        val myField = fields.find { it.name == name }
        if (myField != null) return myField
        var parents = (listOf(superClass) + interfaces).filterNotNull()

        var result = parents.mapNotNull { it as? ConcreteClass }.mapNotNull { it.findFieldConcrete(name) }.firstOrNull()
        while (parents.isNotEmpty()) {
            if (result != null) break
            parents = parents
                    .map { (listOf(it.superClass) + it.interfaces).filterNotNull() }
                    .flatten()
            result = parents.mapNotNull { it as? ConcreteClass }.mapNotNull { it.findFieldConcrete(name) }.firstOrNull()
        }

        return result
                ?: (listOf(superClass) + interfaces).filterNotNull().mapNotNull { it as? OuterClass }.map { it.findFieldConcrete(name) }.firstOrNull()

    }
}

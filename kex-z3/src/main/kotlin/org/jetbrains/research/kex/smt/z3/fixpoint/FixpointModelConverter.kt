package org.jetbrains.research.kex.smt.z3.fixpoint

import com.abdullin.kthelper.collection.dequeOf
import com.microsoft.z3.*
import com.microsoft.z3.enumerations.Z3_decl_kind
import com.microsoft.z3.enumerations.Z3_lbool
import org.jetbrains.research.kex.ktype.*
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.smt.z3.Z3Unlogic
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.*
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.state.transformer.TermCollector
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.ConcreteClass
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.ir.OuterClass
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.type.Type
import org.jetbrains.research.kfg.type.TypeFactory

enum class DependencyType {
    RETURN_VALUE, MEMORY;
}

data class TermDependency(val term: Term, val callIdx: Int, val call: CallPredicate, val type: DependencyType)

data class RecoveredModel(val state: PredicateState, val callDependencies: Set<TermDependency>) {
    val isFinal: Boolean
        get() = callDependencies.isEmpty()

    fun finalStateOrException(): PredicateState = when {
        isFinal -> state
        else -> throw IllegalStateException("State is not final")
    }

    companion object {
        fun error() = RecoveredModel(falseState(), emptySet())
    }
}

class FixpointModelConverter(
        private val mapping: ModelDeclarationMapping,
        private val tf: TypeFactory,
        private val z3Context: Z3Context
) {

    private var callDependencies = hashSetOf<TermDependency>()

    fun apply(expr: Expr): RecoveredModel {
        callDependencies = hashSetOf()
        val state = expr.simplify()
                .let { convert(it) }
                .let { InstanceOfCorrector(z3Context).apply(it) }
                .simplify()
        return RecoveredModel(state, callDependencies.toSet())
    }

    private object UnknownType : KexType() {
        override val name: String = "Unknown"
        override val bitsize: Int = 0
        override fun getKfgType(types: TypeFactory): Type = throw IllegalStateException("type is unknown")
    }

    private class InstanceOfCorrector(private val z3Context: Z3Context) : RecollectingTransformer<InstanceOfCorrector> {

        override val builders = dequeOf(StateBuilder())

        override fun transformEqualityPredicate(predicate: EqualityPredicate): Predicate {
            val unknownInstanceOfTerms = TermCollector { it is InstanceOfTerm && it.checkedType is UnknownType }.apply { transform(predicate) }.terms
            when {
                unknownInstanceOfTerms.isEmpty() -> return super.transformEqualityPredicate(predicate)
                unknownInstanceOfTerms.size != 1 ->
                    throw IllegalStateException("To many unknown instance of checks")
            }
            val rhv = predicate.rhv as? ConstBoolTerm
                    ?: throw IllegalStateException("Unexpected term in $predicate")
            val lhv = predicate.lhv as? CmpTerm
                    ?: throw IllegalStateException("Unexpected term in $predicate")
            val instanceOfTerm = lhv.lhv as? InstanceOfTerm
                    ?: throw IllegalStateException("Unexpected term in $predicate")
            val typeBound = lhv.rhv as? ConstIntTerm
                    ?: throw IllegalStateException("Unexpected term in $predicate")
            val constraints = generateInstanceOfConstraints(instanceOfTerm.operand, lhv.opcode, typeBound.value, predicate)
            val resultConstraint = when (rhv.value) {
                true -> constraints
                false -> NegationState(constraints)
            }
            currentBuilder += resultConstraint
            return nothing()
        }

        private fun generateInstanceOfConstraints(term: Term, cmp: CmpOpcode, typeBound: Int, original: Predicate): PredicateState {
            val predicate = cmp.predicate()
            return z3Context.getTypeMapping().entries
                    .filter { predicate(it.value, typeBound) }
                    .map { it.key }
                    .toSet()
                    .map { generateInstanceOf(term, it, original) }
                    .let { ChoiceState(it) }
        }

        private fun generateInstanceOf(term: Term, candidate: KexType, original: Predicate): PredicateState =
                predicate(original.type, original.location) {
                    InstanceOfTerm(candidate, term) equality const(true)
                }.wrap()

        private fun CmpOpcode.predicate(): (Int, Int) -> Boolean = when (this) {
            is CmpOpcode.Eq -> { a, b -> a == b }
            is CmpOpcode.Neq -> { a, b -> a != b }
            is CmpOpcode.Lt -> { a, b -> a < b }
            is CmpOpcode.Gt -> { a, b -> a > b }
            is CmpOpcode.Le -> { a, b -> a <= b }
            is CmpOpcode.Ge -> { a, b -> a >= b }
            else -> throw IllegalStateException("Unsupported $this")
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
        expr is RealExpr -> convertRealTerm(expr)
        else -> TODO()
    }

    private fun convertVariableTerm(expr: Expr): TermWithAxiom = mapping.getTerm(expr.index, callDependencies)
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
        expr.isRealToInt -> expr.convertArgs().first().transformTerm { it `as` KexInt() }
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
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_ADD -> listOf(expr.args[1], expr.args[2]).map { convertTerm(it) }.combine { a, b -> a add b }
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_TO_FP -> convertTerm(expr.args[1])
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_NEG -> convertTerm(expr.args[0]).transformTerm { it.not() }
        else -> TODO()
    }

    private fun convertRealTerm(expr: RealExpr): TermWithAxiom = when {
        expr is RatNum -> TermWithAxiom.wrap { const(expr.numerator.int64.toDouble() / expr.denominator.int64.toDouble()) }
        expr.isAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isMul -> expr.convertArgs().combine { a, b -> a mul b }
        expr.isIntToReal -> expr.convertArgs().first().transformTerm { it `as` KexDouble() }
        expr.isApp && (expr.funcDecl.name as? StringSymbol)?.string == "fp.to_real" -> expr.convertArgs().first()
        else -> TODO("Real: $expr")
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
            decl is DeclarationTracker.Declaration.Call.CallProperty -> readCallProperty(convertTerm(location), decl)
            else -> throw IllegalStateException("Unexpected memory $memory : $decl")
        }
    }

    private fun readCallProperty(obj: TermWithAxiom, property: DeclarationTracker.Declaration.Call.CallProperty): TermWithAxiom {
        val callInfo = mapping.calls[property.index]!!
        if (property !is DeclarationTracker.Declaration.Call.CallClassProperty) TODO("Not yet implemented")
        val owner = when {
            obj.term.type.getKfgType(tf) is ClassType -> obj.term
            obj.term is ConstIntTerm -> {
                val locals = z3Context.getLocalsTypeMapping()
                val type = locals[obj.term.value] ?: throw IllegalStateException("No type info about local variable")
                term { value(type, "local__${obj.term.value}") }
            }
            else -> throw IllegalArgumentException("Only class types supported")
        }
        val fieldLoad = getFieldLoad(owner, tf.cm[property.className], property.propertyName)
        val loadTerm = obj.binaryOperation(fieldLoad) { _, load -> load }
        callDependencies.add(TermDependency(loadTerm.term, callInfo.index, callInfo.predicate, DependencyType.MEMORY))
        return loadTerm
    }

    private fun readProperty(obj: TermWithAxiom, property: DeclarationTracker.Declaration.Property): TermWithAxiom = when (property) {
        is DeclarationTracker.Declaration.ClassProperty -> {
            val owner = when {
                obj.term.type.getKfgType(tf) is ClassType -> obj.term
                obj.term is ConstIntTerm -> {
                    val locals = z3Context.getLocalsTypeMapping()
                    val type = locals[obj.term.value]
                            ?: throw IllegalStateException("No type info about local variable")
                    term { value(type, "local__${obj.term.value}") }
                }
                else -> throw IllegalArgumentException("Only class types supported")
            }
            val fieldLoad = getFieldLoad(owner, tf.cm[property.className], property.propertyName)
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
        val fieldType = fields.map { it.type.kexType }.groupBy({ it }, { 1 }).maxByOrNull { (_, cnt) -> cnt.sum() }?.key
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
            .reduce { t1: Term, t2: Term -> term { t1 or t2 } }

    private fun Class.allInheritors() = cm.concreteClasses.filter { it.isInheritorOf(this) }.toSet()

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

package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.*
import com.microsoft.z3.enumerations.Z3_lbool
import org.jetbrains.research.kex.ktype.*
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.smt.z3.Z3Unlogic
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.ConstantPropagator
import org.jetbrains.research.kex.state.transformer.Optimizer
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.TypeIndex
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.type.Type
import org.jetbrains.research.kfg.type.TypeFactory

class FixpointModelConverter(
        private val mapping: ModelDeclarationMapping,
        private val tf: TypeFactory
) {

    object UnknownType : KexType() {
        override val name: String = "Unknown"
        override val bitsize: Int = 0
        override fun getKfgType(types: TypeFactory): Type = throw IllegalStateException("type is unknown")
    }

    class InstanceOfCorrector : Transformer<InstanceOfCorrector> {
        class UnknownInstanceOfCollector : Transformer<UnknownInstanceOfCollector> {
            val predicatesToCorrect = arrayListOf<EqualityPredicate>()
            override fun transformEqualityPredicate(predicate: EqualityPredicate): Predicate {
                if (instanceOfPattern(predicate)) {
                    predicatesToCorrect.add(predicate)
                }
                return super.transformEqualityPredicate(predicate)
            }

            fun instanceOfPattern(predicate: EqualityPredicate): Boolean {
                if (predicate.rhv !is ConstBoolTerm) return false
                val lhv = predicate.lhv as? CmpTerm ?: return false
                val instanceOf = lhv.lhv as? InstanceOfTerm ?: return false
                return instanceOf.checkedType is UnknownType
            }
        }

        class PredicateRemapping(val mapping: Map<Predicate, Predicate>) : Transformer<PredicateRemapping> {
            override fun transformPredicate(predicate: Predicate) = mapping[predicate]
                    ?: super.transformPredicate(predicate)
        }

        override fun apply(ps: PredicateState): PredicateState {
            val unknownInstanceOf = UnknownInstanceOfCollector().apply { apply(ps) }.predicatesToCorrect
            if (unknownInstanceOf.isEmpty()) return ps
            val normalized = unknownInstanceOf.map { normalize(it) }
            for (condition in normalized) {
                condition.findUnknownBound(normalized)
            }
            if (normalized.any { it.isUnknown() }) throw IllegalStateException("Unable to restore types")
            val instanceOfTerms = normalized.map { InstanceOfTerm(TypeIndex.findType(it.typeIdx()), it.arg) }
            val predicates = unknownInstanceOf.zip(instanceOfTerms).map { (predicate, term) ->
                EqualityPredicate(term, ConstBoolTerm(true), predicate.type, predicate.location)
            }
            val mapping = unknownInstanceOf.zip(predicates).toMap<Predicate, Predicate>()
            return PredicateRemapping(mapping).apply(ps)
        }

        data class InstanceOfCondition(val arg: Term, var upperBound: Int = UNKNOWN, var lowerBound: Int = UNKNOWN) {
            fun typeIdx() = lowerBound + 1
            fun isUnknown() = upperBound == UNKNOWN || lowerBound == UNKNOWN || upperBound != lowerBound + 2
            fun findUnknownBound(conditions: List<InstanceOfCondition>) {
                if (lowerBound == UNKNOWN && upperBound != UNKNOWN) {
                    val other = conditions.find { it.lowerBound + 1 == upperBound - 1 }
                            ?: throw IllegalStateException("Unable to find lower bound")
                    lowerBound = other.lowerBound
                    other.upperBound = upperBound
                }
                if (lowerBound != UNKNOWN && upperBound == UNKNOWN) {
                    val other = conditions.find { it.upperBound - 1 == lowerBound + 1 }
                            ?: throw IllegalStateException("Unable to find upper bound")
                    upperBound = other.upperBound
                    other.lowerBound = lowerBound
                }
            }

            companion object {
                const val UNKNOWN = -10
            }
        }

        private fun normalize(predicate: EqualityPredicate): InstanceOfCondition {
            val isTrue = (predicate.rhv as ConstBoolTerm).value
            val cmp = predicate.lhv as CmpTerm
            val bound = (cmp.rhv as ConstIntTerm).value
            val arg = (cmp.lhv as InstanceOfTerm).operand
            return when {
                isTrue && cmp.opcode is CmpOpcode.Gt -> InstanceOfCondition(arg, lowerBound = bound)
                isTrue && cmp.opcode is CmpOpcode.Lt -> InstanceOfCondition(arg, upperBound = bound)
                !isTrue && cmp.opcode is CmpOpcode.Le -> InstanceOfCondition(arg, lowerBound = bound)
                !isTrue && cmp.opcode is CmpOpcode.Ge -> InstanceOfCondition(arg, upperBound = bound)
                else -> TODO("Unexpected cmp term: $cmp")
            }
        }
    }

    fun apply(expr: Expr): PredicateState = expr.simplify()
            .let { convert(it) }
            .let { InstanceOfCorrector().apply(it) }
            .let { ConstantPropagator.apply(it) }
            .let { Optimizer().apply(it) }
            .simplify()

    private fun convert(expr: Expr): PredicateState = when (expr) {
        is BoolExpr -> convert(expr)
        else -> convertTerm(expr).equality { const(true) }
    }

    private fun convertTerm(expr: Expr): TermWithAxiom = when {
        expr.isVar -> variableTerm(expr)
        expr is BoolExpr -> convertTerm(expr)
        expr is IntExpr -> convertTerm(expr)
        expr is BitVecExpr -> convertTerm(expr)
        expr is FPExpr -> convertTerm(expr)
        else -> TODO()
    }

    private fun variableTerm(expr: Expr): TermWithAxiom {
        val term = mapping.getTerm(expr.index)
        return when {
            term is CallTerm -> {
                val value = term { value(term.type, "call__${expr.index}") }
                val axiom = basic {
                    state { value.call(term) }
                }
                TermWithAxiom(value, axiom)
            }
            else -> TermWithAxiom(term)
        }
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

    private fun convertTerm(expr: BoolExpr): TermWithAxiom = when {
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

    private fun convertTerm(expr: IntExpr): TermWithAxiom = when {
        expr.isIntNum -> TermWithAxiom.wrap { const((expr as IntNum).int) }
        expr.isAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isMul -> expr.convertArgs().combine { a, b -> a mul b }
        expr.isSelect && expr.numArgs == 2 -> convertMemoryLoad(expr.args[0], expr.args[1])
        else -> TODO()
    }

    private fun convertTerm(expr: BitVecExpr): TermWithAxiom = when {
        expr is BitVecNum -> TermWithAxiom.wrap { Z3Unlogic.undo(expr) }
        expr.isBVAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isBVMul -> expr.convertArgs().combine { a, b -> a mul b }
        expr.isSelect && expr.numArgs == 2 -> convertMemoryLoad(expr.args[0], expr.args[1])
        else -> TODO()
    }

    private fun convertTerm(expr: FPExpr): TermWithAxiom = when {
        expr is FPNum -> TermWithAxiom.wrap { Z3Unlogic.undo(expr) }
        else -> TODO()
    }

    private fun convertMemoryLoad(memory: Expr, location: Expr): TermWithAxiom {
        if (!memory.isVar) throw IllegalStateException("Memory is not var $memory")
        val decl = mapping.declarations[memory.index]
        return when {
            decl is DeclarationTracker.Declaration.Property -> when {
                location.isVar -> {
                    variableTerm(location).transformTerm { readProperty(it, decl) }
                }
                else -> TODO("Property location is not var")
            }
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

    private fun readProperty(obj: Term, property: DeclarationTracker.Declaration.Property): Term = when (property) {
        is DeclarationTracker.Declaration.ClassProperty -> {
            val kType = obj.type.getKfgType(tf)
            if (kType !is ClassType) {
                TODO("Only class types supported")
            }
            val kfgClass = kType.`class`
            if (kfgClass.fullname != property.className) {
                throw IllegalArgumentException("Class $kfgClass doesn't match property $property")
            }
            val field = kfgClass.fields.find { it.name == property.propertyName }
                    ?: throw IllegalArgumentException("Class $kfgClass has no property $property")
            term { obj.field(field.type.kexType, field.name).load() }
        }
        else -> when {
            property.fullName == Z3Context.TYPE_PROPERTY -> InstanceOfTerm(UnknownType, obj)
            obj.type is KexArray && property.fullName == "length" -> ArrayLengthTerm(KexInt(), obj)
            else -> TODO("Unknown property $property")
        }

    }

    private data class TermWithAxiom(val term: Term, val axiom: PredicateState? = null) {

        fun equality(other: TermWithAxiom): PredicateState {
            val predicate = state { term equality other.term }
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
}

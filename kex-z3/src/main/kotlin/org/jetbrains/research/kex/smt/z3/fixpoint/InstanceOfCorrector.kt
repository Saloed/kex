package org.jetbrains.research.kex.smt.z3.fixpoint

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.predicate
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.state.transformer.TermCollector
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode
import org.jetbrains.research.kfg.type.Type
import org.jetbrains.research.kfg.type.TypeFactory

internal object UnknownType : KexType() {
    override val name: String = "Unknown"
    override val bitsize: Int = 0
    override fun getKfgType(types: TypeFactory): Type = throw IllegalStateException("type is unknown")
}

internal class InstanceOfCorrector(private val z3Context: Z3Context) : RecollectingTransformer<InstanceOfCorrector> {

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
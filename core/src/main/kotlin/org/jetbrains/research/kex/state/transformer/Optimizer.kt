package org.jetbrains.research.kex.state.transformer

import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.ConstantPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.term.ConstBoolTerm
import org.jetbrains.research.kex.state.term.term

class Optimizer : Transformer<Optimizer> {

    override fun transformChain(ps: ChainState): PredicateState {
        val base = transform(ps.base)
        val curr = transform(ps.curr)
        return when {
            base.evaluatesToFalse || curr.evaluatesToFalse -> falseState()
            base.evaluatesToTrue && curr.evaluatesToTrue -> trueState()
            else -> merge(base, curr)
        }
    }

    override fun transformBasicState(ps: BasicState): PredicateState = when {
        ps.evaluatesToFalse -> falseState()
        ps.evaluatesToTrue -> trueState()
        else -> ps.filterNot { it is ConstantPredicate }
    }

    override fun transformNegation(ps: NegationState): PredicateState {
        val nested = transform(ps.predicateState)
        return when {
            nested.evaluatesToFalse -> trueState()
            nested.evaluatesToTrue -> falseState()
            else -> simplifyNegation(nested)
        }
    }

    private fun simplifyNegation(ps: PredicateState): PredicateState {
        if (ps !is BasicState) return NegationState(ps)
        val equalities = ps.predicates.filterIsInstance<EqualityPredicate>()
        if (equalities != ps.predicates) return NegationState(ps)
        val boolEqualities = equalities.filter { it.rhv is ConstBoolTerm }
        if (boolEqualities != ps.predicates) return NegationState(ps)
        val simplifiedPredicates = boolEqualities.map {
            val rhv = it.rhv as ConstBoolTerm
            val newRhv = term { const(!rhv.value) }
            EqualityPredicate(it.lhv, newRhv, it.type, it.location)
        }
        return BasicState(simplifiedPredicates)
    }

    override fun transformChoice(ps: ChoiceState): PredicateState {
        val choices = ps.choices.map { transform(it) }
        if (choices.any { it.evaluatesToTrue }) return trueState()
        val nonFalseChoices = choices.filterNot { it.evaluatesToFalse }
        if (nonFalseChoices.isEmpty()) return falseState()
        return ChoiceState(nonFalseChoices)
    }

    private fun merge(first: PredicateState, second: PredicateState): PredicateState = when {
        first is BasicState && second is BasicState -> BasicState(first.predicates + second.predicates)
        first is ChainState && first.curr is BasicState && second is BasicState -> {
            val merged = BasicState(first.curr.predicates + second.predicates)
            ChainState(first.base, merged)
        }
        first is BasicState && second is ChainState && second.base is BasicState -> {
            val merged = BasicState(first.predicates + second.base.predicates)
            ChainState(merged, second.curr)
        }
        else -> ChainState(first, second)
    }
}

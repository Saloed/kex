package org.jetbrains.research.kex.asm.analysis.refinements

import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.not
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.ConstBoolTerm
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kex.util.join
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.type.Type


data class RefinementCriteria(val type: Type)

data class Refinement private constructor(val criteria: RefinementCriteria, val state: PredicateState) {
    fun expand(others: List<PredicateState>): Refinement {
        val negateOtherPaths = ChoiceState(others).not()
        val expandedState = ChainState(state, negateOtherPaths).optimize()
        return Refinement(criteria, expandedState)
    }

    fun fmap(transform: (PredicateState) -> PredicateState) = Refinement(criteria, transform(state))

    fun merge(other: Refinement): Refinement {
        if (criteria != other.criteria) throw IllegalArgumentException("Try to merge different refinement sources")
        val mergedCondition = ChoiceState(listOf(state, other.state)).optimize()
        return Refinement(criteria, mergedCondition)
    }

    companion object {
        fun create(criteria: RefinementCriteria, state: PredicateState): Refinement {
            val ensurePathPredicatesInState = state.map {
                when {
                    it is EqualityPredicate && it.rhv is ConstBoolTerm -> EqualityPredicate(it.lhv, it.rhv, PredicateType.Path(), it.location)
                    else -> it
                }
            }
            return Refinement(criteria, ensurePathPredicatesInState)
        }
    }
}

data class Refinements(val value: List<Refinement>, val method: Method) {
    fun expanded(): Refinements = value
            .map { reft ->
                val others = value.filter { it.criteria != reft.criteria }
                val otherSates = others.map { it.state }
                reft.expand(otherSates)
            }
            .let { Refinements(it, method) }

    fun allStates(): PredicateState = ChoiceState(value.map { it.state })
    fun merge(other: Refinements) = merge(this, other)
    fun fmap(transform: (PredicateState) -> PredicateState) = Refinements(value.map { it.fmap(transform) }, method)

    fun isUnknown() = value.isEmpty()

    companion object {
        fun unknown(method: Method) = Refinements(emptyList(), method)
    }
}

data class RefinementSources(val value: List<RefinementSource>) {
    fun simplify() = merge(RefinementSources(emptyList()))
    fun merge(other: RefinementSources): RefinementSources = merge(this, other)
    fun fmap(transform: (PredicateState) -> PredicateState) = RefinementSources(value.map { it.fmap(transform) })
}

data class RefinementSource(val criteria: RefinementCriteria, val condition: PredicateState) {
    fun merge(other: RefinementSource): RefinementSource {
        if (criteria != other.criteria) throw IllegalArgumentException("Try to merge different refinement sources")
        val mergedCondition = ChoiceState(listOf(condition, other.condition)).optimize()
        return RefinementSource(criteria, mergedCondition)
    }

    fun fmap(transform: (PredicateState) -> PredicateState) = RefinementSource(criteria, transform(condition))
}

private fun merge(first: RefinementSources, second: RefinementSources): RefinementSources {
    val lhs = first.value.groupBy { it.criteria }
    val rhs = second.value.groupBy { it.criteria }
    val merged = (lhs.keys + rhs.keys).map {
        ((lhs[it] ?: emptyList()) + (rhs[it] ?: emptyList())).join { a, b -> a.merge(b) }
    }
    return RefinementSources(merged)
}

private fun merge(first: Refinements, second: Refinements): Refinements {
    val lhs = first.value.groupBy { it.criteria }
    val rhs = second.value.groupBy { it.criteria }
    val merged = (lhs.keys + rhs.keys).map {
        ((lhs[it] ?: emptyList()) + (rhs[it] ?: emptyList())).join { a, b -> a.merge(b) }
    }
    return Refinements(merged, first.method)
}

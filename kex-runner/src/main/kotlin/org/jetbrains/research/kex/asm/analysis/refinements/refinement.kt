package org.jetbrains.research.kex.asm.analysis.refinements

import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.not
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.type.Type

data class RefinementCriteria(val type: Type)

data class Refinement(val criteria: RefinementCriteria, val state: PredicateState) {
    fun expand(others: List<PredicateState>): Refinement {
        val negateOtherPaths = ChoiceState(others).not()
        val expandedState = ChainState(state, negateOtherPaths).optimize()
        return Refinement(criteria, expandedState)
    }

    fun fmap(transform: (PredicateState) -> PredicateState) = Refinement(criteria, transform(state))
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
    fun fmap(transform: (PredicateState) -> PredicateState) = Refinements(value.map { it.fmap(transform) }, method)

    companion object {
        fun unknown(method: Method) = Refinements(emptyList(), method)
    }
}

data class RefinementSources(val value: List<RefinementSource>) {

    fun simplify() = merge(RefinementSources(emptyList()))

    fun merge(other: RefinementSources): RefinementSources {
        val lhs = value.groupBy { it.criteria }
        val rhs = other.value.groupBy { it.criteria }
        val merged = (lhs.keys + rhs.keys).map {
            merge((lhs[it] ?: emptyList()) + (rhs[it] ?: emptyList()))
        }
        return RefinementSources(merged)
    }

    fun fmap(transform: (PredicateState) -> PredicateState) = RefinementSources(value.map { it.fmap(transform) })

    private fun merge(sources: List<RefinementSource>): RefinementSource = when (sources.size) {
        1 -> sources.first()
        else -> sources.drop(1).fold(sources.first()) { acc, refinementSource -> acc.merge(refinementSource) }
    }
}

data class RefinementSource(val criteria: RefinementCriteria, val condition: PredicateState) {
    fun merge(other: RefinementSource): RefinementSource {
        if (criteria != other.criteria) throw IllegalArgumentException("Try to merge different refinement sources")
        val mergedCondition = ChoiceState(listOf(condition, other.condition)).optimize()
        return RefinementSource(criteria, mergedCondition)
    }

    fun fmap(transform: (PredicateState) -> PredicateState) = RefinementSource(criteria, transform(condition))
}

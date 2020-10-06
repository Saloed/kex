package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.ConstantPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.type.Type

data class RefinementCriteria(val type: Type)

data class PathConditions(val pc: Map<RefinementCriteria, PredicateState>) {
    fun noErrorCondition(): PredicateState = chain(pc.values.map { it.not() })
    fun fmap(transformer: (RefinementCriteria, PredicateState) -> PredicateState) = PathConditions(pc.mapValues { (criteria, terms) -> transformer(criteria, terms) })

    fun merge(others: List<PathConditions>): PathConditions {
        val entries = others.flatMap { it.pc.entries } + pc.entries
        val merged = entries.groupBy({ it.key }, { it.value }).mapValues { (_, paths) -> chain(paths) }
        return PathConditions(merged)
    }

    fun expandedErrorConditions() = pc.mapValues { (criteria, _) -> expandedErrorCondition(criteria) }

    fun expandedErrorCondition(criteria: RefinementCriteria): PredicateState {
        val conditionVariables = pc[criteria] ?: error("No criteria $criteria")
        val otherVariables = pc.filter { it.key != criteria }.values
        val noOtherErrors = chain(otherVariables.map { it.not() })
        return ChainState(conditionVariables, noOtherErrors)
    }
}

data class Refinement private constructor(val criteria: RefinementCriteria, val state: PredicateStateWithPath) {
    fun expand(others: List<PredicateStateWithPath>): Refinement {
        val negateOtherPaths = others.map { it.negate() }.let { PredicateStateWithPath.chain(it) }
        val expandedState = PredicateStateWithPath.chain(listOf(state, negateOtherPaths))
        return Refinement(criteria, expandedState)
    }

    fun fmap(transform: (PredicateStateWithPath) -> PredicateStateWithPath) = Refinement(criteria, transform(state))

    fun merge(other: Refinement): Refinement {
        if (criteria != other.criteria) throw IllegalArgumentException("Try to merge different refinement conditions")
        val mergedCondition = PredicateStateWithPath.choice(listOf(state, other.state))
        return Refinement(criteria, mergedCondition)
    }

    override fun toString(): String = "$criteria -> $state"

    companion object {
        fun create(criteria: RefinementCriteria, state: PredicateStateWithPath) = Refinement(criteria, state)
    }
}

data class Refinements private constructor(val value: List<Refinement>, val method: Method) {

    fun expanded(): Refinements = value
            .map { reft ->
                val others = value.filter { it.criteria != reft.criteria }
                val otherSates = others.map { it.state }
                reft.expand(otherSates)
            }
            .let { Refinements(it, method) }

    fun merge(other: Refinements): Refinements {
        val lhs = this.value.groupBy { it.criteria }
        val rhs = other.value.groupBy { it.criteria }
        val merged = (lhs.keys + rhs.keys).map {
            ((lhs[it] ?: emptyList()) + (rhs[it] ?: emptyList())).reduce { a, b -> a.merge(b) }
        }
        return Refinements(merged, method)
    }

    fun fmap(transform: (PredicateStateWithPath) -> PredicateStateWithPath) = Refinements(value.map { it.fmap(transform) }, method)

    fun allStates(): PredicateState = ChoiceState(value.map { it.state.toPredicateState() })
    fun isUnknown() = value.isEmpty()

    override fun toString(): String = "Refinements $method: \n" + value.joinToString("\n") { "$it" }

    companion object {
        fun unknown(method: Method) = Refinements(emptyList(), method)
        fun create(method: Method, refinements: List<Refinement>) = Refinements(refinements, method)
    }
}

data class RefinementSources private constructor(val value: List<RefinementSource>) {
    fun expanded(): RefinementSources = value
            .map { reft ->
                val others = value.filter { it.criteria != reft.criteria }
                val otherSates = others.map { it.state }
                reft.expand(otherSates)
            }
            .let { RefinementSources(it) }

    fun merge(other: RefinementSources): RefinementSources {
        val lhs = this.value.groupBy { it.criteria }
        val rhs = other.value.groupBy { it.criteria }
        val merged = (lhs.keys + rhs.keys).map {
            ((lhs[it] ?: emptyList()) + (rhs[it] ?: emptyList())).reduce { a, b -> a.merge(b) }
        }
        return RefinementSources(merged)
    }

    fun fmap(transform: (PredicateState) -> PredicateState) = RefinementSources(value.map { it.fmap(transform) })
    fun simplify() = merge(empty())
    fun zip(other: RefinementSources): List<Pair<RefinementSource, RefinementSource>> {
        val otherSources = other.value.map { it.criteria to it }.toMap()
        return value.map {
            it to (otherSources[it.criteria] ?: throw IllegalArgumentException("Unable to zip $this and $other"))
        }
    }

    override fun toString(): String = "RefinementSources: \n" + value.joinToString("\n") { "$it" }

    companion object {
        fun empty() = RefinementSources(emptyList())
        fun create(sources: List<RefinementSource>) = RefinementSources(sources)
    }
}

data class RefinementSource private constructor(val criteria: RefinementCriteria, val state: PredicateState) {
    val condition: PredicateState = state
    fun expand(others: List<PredicateState>): RefinementSource {
        val negateOtherPaths = ChoiceState(others).negateWRTStatePredicates()
        val expandedState = ChainState(state, negateOtherPaths)
        return RefinementSource(criteria, expandedState)
    }

    fun fmap(transform: (PredicateState) -> PredicateState) = RefinementSource(criteria, transform(state))

    fun merge(other: RefinementSource): RefinementSource {
        if (criteria != other.criteria) throw IllegalArgumentException("Try to merge different refinement conditions")
        val mergedCondition = ChoiceState(listOf(state, other.state))
        return RefinementSource(criteria, mergedCondition)
    }

    override fun toString(): String = "$criteria -> $state"

    companion object {
        fun create(criteria: RefinementCriteria, state: PredicateState) = RefinementSource(criteria, state)
    }
}

fun PredicateState.negateWRTStatePredicates(): PredicateState = negatePsIgnoringStatePredicates(this)

private fun PredicateState.hasNoStatePredicates() = filter { it !is ConstantPredicate && it.type is PredicateType.State }.isEmpty

private fun negatePsIgnoringStatePredicates(ps: PredicateState): PredicateState {
    if (ps.hasNoStatePredicates()) return NegationState(ps)
    return when (ps) {
        is BasicState -> {
            val indicesToNegate = ps.predicates.withIndex()
                    .filter { it.value.type is PredicateType.Path }
                    .map { it.index }
            val states = arrayListOf<PredicateState>()
            for (indexToNegate in indicesToNegate) {
                val builder = StateBuilder()
                loop@ for ((index, predicate) in ps.predicates.withIndex()) {
                    when {
                        index < indexToNegate -> builder += predicate
                        index == indexToNegate -> builder += NegationState(predicate.wrap())
                        else -> break@loop
                    }
                }
                states += builder.apply().optimize()
            }
            ChoiceState(states)
        }
        is NegationState -> ps.predicateState
        is ChainState -> when {
            ps.base.hasNoStatePredicates() -> ChoiceState(listOf(ps.base, ps.curr).map { negatePsIgnoringStatePredicates(it) })
            else -> {
                val notBase = negatePsIgnoringStatePredicates(ps.base)
                val notCurr = negatePsIgnoringStatePredicates(ps.curr)
                ChoiceState(listOf(notBase, ChainState(ps.base, notCurr)))
            }
        }
        is ChoiceState -> ps.choices.map { negatePsIgnoringStatePredicates(it) }.reduce { ps1, ps2 -> ChainState(ps1, ps2) }
        else -> throw IllegalStateException("Unknown ps type $ps")
    }
}

package org.jetbrains.research.kex.asm.analysis.refinements

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

data class Refinement private constructor(private val refinementData: RefinementData) : RefinementData {
    override val criteria = refinementData.criteria
    override val state = refinementData.state
    override fun expand(others: List<PredicateState>): Refinement = Refinement(refinementData.expand(others))
    override fun fmap(transform: (PredicateState) -> PredicateState) = Refinement(refinementData.fmap(transform))
    override fun merge(other: RefinementData) = Refinement(refinementData.merge(other))

    override fun toString(): String = "$criteria -> $state"

    companion object {
        fun create(criteria: RefinementCriteria, state: PredicateStateWithPath) = Refinement(RefinementDataImpl(criteria, state))
    }
}

data class Refinements private constructor(private val refinementData: RefinementDataList, val method: Method) : RefinementDataList {
    override val value: List<Refinement> = refinementData.value as List<Refinement>
    override fun merge(other: RefinementDataList) = Refinements(refinementData.merge(other), method)
    override fun expanded(): Refinements = Refinements(refinementData.expanded(), method)
    override fun fmap(transform: (PredicateState) -> PredicateState) = Refinements(refinementData.fmap(transform), method)

    fun allStates(): PredicateState = ChoiceState(value.map { it.state })
    fun isUnknown() = value.isEmpty()

    override fun toString(): String = "Refinements $method: \n" + value.joinToString("\n") { "$it" }

    companion object {
        fun unknown(method: Method) = Refinements(RefinementDataListImpl(emptyList()), method)
        fun create(method: Method, refinements: List<Refinement>) = Refinements(RefinementDataListImpl(refinements), method)
    }
}

data class RefinementSources private constructor(private val refinementData: RefinementDataList) : RefinementDataList {
    override val value: List<RefinementSource> = refinementData.value as List<RefinementSource>
    override fun expanded() = RefinementSources(refinementData.expanded())
    override fun fmap(transform: (PredicateState) -> PredicateState) = RefinementSources(refinementData.fmap(transform))
    override fun merge(other: RefinementDataList) = RefinementSources(refinementData.merge(other))
    fun simplify() = merge(empty())
    fun zip(other: RefinementSources): List<Pair<RefinementSource, RefinementSource>> {
        val otherSources = other.value.map { it.criteria to it }.toMap()
        return value.map {
            it to (otherSources[it.criteria] ?: throw IllegalArgumentException("Unable to zip $this and $other"))
        }
    }

    override fun toString(): String = "RefinementSources: \n" + value.joinToString("\n") { "$it" }

    companion object {
        fun empty() = RefinementSources(RefinementDataListImpl(emptyList()))
        fun create(sources: List<RefinementSource>) = RefinementSources(RefinementDataListImpl(sources))
    }
}

data class RefinementSource private constructor(private val refinementData: RefinementData) : RefinementData {
    override val state: PredicateState = refinementData.state
    override val criteria: RefinementCriteria = refinementData.criteria
    val condition: PredicateState = state

    override fun expand(others: List<PredicateState>) = RefinementSource(refinementData.expand(others))
    override fun fmap(transform: (PredicateState) -> PredicateState) = RefinementSource(refinementData.fmap(transform))
    override fun merge(other: RefinementData) = RefinementSource(refinementData.merge(other))

    override fun toString(): String = "$criteria -> $state"

    companion object {
        fun create(criteria: RefinementCriteria, state: PredicateState) = RefinementSource(RefinementDataImpl(criteria, state))
    }
}

interface RefinementData {
    val criteria: RefinementCriteria
    val state: PredicateStateWithPath
    fun expand(others: List<PredicateState>): RefinementData
    fun fmap(transform: (PredicateState) -> PredicateState): RefinementData
    fun merge(other: RefinementData): RefinementData
}

interface RefinementDataList {
    val value: List<RefinementData>
    fun expanded(): RefinementDataList
    fun merge(other: RefinementDataList): RefinementDataList
    fun fmap(transform: (PredicateState) -> PredicateState): RefinementDataList
}

private data class RefinementDataImpl(override val criteria: RefinementCriteria, override val state: PredicateStateWithPath) : RefinementData {
    override fun expand(others: List<PredicateState>): RefinementData {
        val negateOtherPaths = ChoiceState(others).negateWRTStatePredicates()
        val expandedState = ChainState(state, negateOtherPaths)
        return RefinementDataImpl(criteria, expandedState)
    }

    override fun fmap(transform: (PredicateState) -> PredicateState) = RefinementDataImpl(criteria, transform(state))

    override fun merge(other: RefinementData): RefinementData {
        if (criteria != other.criteria) throw IllegalArgumentException("Try to merge different refinement conditions")
        val mergedCondition = ChoiceState(listOf(state, other.state))
        return RefinementDataImpl(criteria, mergedCondition)
    }
}

private data class RefinementDataListImpl(override val value: List<RefinementData>) : RefinementDataList {
    override fun expanded(): RefinementDataList = value
            .map { reft ->
                val others = value.filter { it.criteria != reft.criteria }
                val otherSates = others.map { it.state }
                reft.expand(otherSates)
            }
            .let { RefinementDataListImpl(it) }

    override fun merge(other: RefinementDataList): RefinementDataList {
        val lhs = this.value.groupBy { it.criteria }
        val rhs = other.value.groupBy { it.criteria }
        val merged = (lhs.keys + rhs.keys).map {
            ((lhs[it] ?: emptyList()) + (rhs[it] ?: emptyList())).reduce { a, b -> a.merge(b) }
        }
        return RefinementDataListImpl(merged)
    }

    override fun fmap(transform: (PredicateState) -> PredicateState) = RefinementDataListImpl(value.map { it.fmap(transform) })
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

package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.MemoryAccessType
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.InequalityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.state.transformer.Transformer


private class MyNewPathPredicateToPathVariableTransformer(private val variableGenerator: VariableGenerator) : RecollectingTransformer<MyNewPathPredicateToPathVariableTransformer> {
    override val builders = dequeOf(StateBuilder())
    val createdPathVars = arrayListOf<Term>()
    override fun transformPredicate(predicate: Predicate): Predicate {
        if (predicate.type != PredicateType.Path()) return super.transformPredicate(predicate)
        val pathVar = variableGenerator.generatorFor(predicate).createVar(KexBool())
        createdPathVars += pathVar
        val pathCondition = when (predicate) {
            is EqualityPredicate -> term { predicate.lhv eq predicate.rhv }
            is InequalityPredicate -> term { predicate.lhv neq predicate.rhv }
            else -> error("Unsupported predicate $predicate")
        }
        currentBuilder += EqualityPredicate(pathVar, pathCondition, PredicateType.State(), predicate.location)
        currentBuilder += EqualityPredicate(pathVar, term { const(true) }, PredicateType.Path(), predicate.location)
        return nothing()
    }
}

fun collapseStatePredicates(state: PredicateState): PredicateState = when (state) {
    is BasicState -> collapseStatePredicates(state)
    is ChainState -> collapseStatePredicates(state)
    is ChoiceState -> collapseStatePredicates(state)
    else -> error("State collapse is unsupported for $state")
}

fun collapseStatePredicates(state: ChoiceState): PredicateState {
    val collapsedChoices = state.choices.map { collapseStatePredicates(it) }
    val successfullyCollapsedChoices = collapsedChoices.castElementsOrNull<BasicState>() ?: TODO("Not collapsed")
    val memoryAccess = successfullyCollapsedChoices.flatMap { MemoryUtils.collectMemoryAccesses(it) }
    if (memoryAccess.any { it.accessType == MemoryAccessType.WRITE }) {
        TODO("Unable to collapse memory write")
    }
    return BasicState(successfullyCollapsedChoices.flatMap { it.predicates })
}

fun collapseStatePredicates(state: BasicState): PredicateState = state
fun collapseStatePredicates(state: ChainState): PredicateState {
    val collapsedBase = collapseStatePredicates(state.base)
    val collapsedCurr = collapseStatePredicates(state.curr)
    return when {
        collapsedBase is BasicState && collapsedCurr is BasicState -> BasicState(collapsedBase.predicates + collapsedCurr.predicates)
        else -> ChainState(collapsedBase, collapsedCurr)
    }
}

fun createPathCondition(state: PredicateState): Pair<PredicateState, PredicateState> {
    val variableGenerator = VariableGenerator("call_resolve").unique()
    val transformer = MyNewPathPredicateToPathVariableTransformer(variableGenerator)
    val fullState = transformer.apply(state)
    val resultState = fullState.filterByType(PredicateType.State())
    val resultPath = fullState.filterByType(PredicateType.Path())
    val ultraResultState = collapseStatePredicates(resultState)
    return ultraResultState to resultPath
}

inline fun <reified T> List<*>.castElementsOrNull() = filterIsInstance<T>().takeIf { size == it.size }

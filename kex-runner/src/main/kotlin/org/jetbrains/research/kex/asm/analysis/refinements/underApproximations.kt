package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.state.transformer.optimize


class MethodApproximationManager {
    val underApproximations = hashMapOf<CallPredicate, MethodUnderApproximations>()
    fun update(call: CallPredicate, approximation: MethodUnderApproximation) {
        val currentApproximations = underApproximations.getOrDefault(call, MethodUnderApproximations())
        underApproximations[call] = currentApproximations.add(approximation)
    }

    fun extendWithUnderApproximations(state: PredicateState): PredicateState = ApproximationInliner(underApproximations).apply(state).optimize()
}

data class MethodUnderApproximation(val pre: PredicateState, val post: PredicateState)
data class MethodUnderApproximations(val approximations: Set<MethodUnderApproximation> = emptySet()) {
    fun add(approximation: MethodUnderApproximation) = MethodUnderApproximations(approximations + approximation)
}


class ApproximationInliner(val approximations: Map<CallPredicate, MethodUnderApproximations>) : RecollectingTransformer<ApproximationInliner> {
    override val builders = dequeOf(StateBuilder())

    @OptIn(ExperimentalStdlibApi::class)
    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val transformedCall = super.transformCallPredicate(predicate) as CallPredicate
        val approximation = approximations[transformedCall]?.approximations
        val preconditions = approximation?.map { it.pre } ?: emptyList()
        val postconditions = approximation?.map { it.post } ?: emptyList()
        val defaultPostcondition = postconditions.map { it.not() }
                .reduceOrNull<PredicateState, PredicateState> { a, b -> ChainState(a, b) }
                ?: emptyState()
        currentBuilder += CallApproximationState(preconditions, postconditions, transformedCall, defaultPostcondition)
        return nothing()
    }
}

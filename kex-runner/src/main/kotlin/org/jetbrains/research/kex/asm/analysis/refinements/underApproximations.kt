package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.util.join


class MethodApproximationManager {
    val underApproximations = hashMapOf<CallPredicate, MethodUnderApproximations>()
    fun update(call: CallPredicate, approximation: MethodUnderApproximation) {
        val currentApproximations = underApproximations.getOrDefault(call, MethodUnderApproximations())
        underApproximations[call] = currentApproximations.add(approximation)
    }

    fun extendWithUnderApproximations(state: PredicateState): PredicateState = ApproximationInliner(underApproximations).apply(state)
}

data class MethodUnderApproximation(val pre: PredicateState, val post: PredicateState)
data class MethodUnderApproximations(val approximations: Set<MethodUnderApproximation> = emptySet()) {
    fun add(approximation: MethodUnderApproximation) = MethodUnderApproximations(approximations + approximation)
}


class ApproximationInliner(val approximations: Map<CallPredicate, MethodUnderApproximations>) : RecollectingTransformer<ApproximationInliner> {
    override val builders = dequeOf(StateBuilder())
    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val transformedCall = super.transformCallPredicate(predicate)
        val approximation = approximations[transformedCall] ?: return transformedCall
        val cases = approximation.approximations.map { it.pre to it.post }.toMap()
        val defaultCase = approximation.approximations.map { it.post.not() }.join(emptyState()) { a, b -> ChainState(a, b) }
        currentBuilder += SwitchState(cases, ChainState(transformedCall.wrap(), defaultCase))
        return nothing()
    }
}
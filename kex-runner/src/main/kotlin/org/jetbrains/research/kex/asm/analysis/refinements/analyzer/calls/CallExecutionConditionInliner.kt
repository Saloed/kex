package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.asm.analysis.refinements.PathConditions
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer

class CallExecutionConditionInliner private constructor(
        private val callPathConditions: Map<CallPredicate, PathConditions>
) : RecollectingTransformer<CallExecutionConditionInliner> {
    override val builders = dequeOf(StateBuilder())
    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val conditions = callPathConditions[predicate] ?: return nothing()
        currentBuilder += conditions.noErrorCondition()
        return nothing()
    }

    override fun apply(ps: PredicateState): PredicateState {
        builders.clear()
        builders += StateBuilder()
        return super.apply(ps)
    }

    companion object {
        fun normalExecutionConditions(
                state: PredicateState,
                call: CallPredicate,
                callPathConditions: Map<CallPredicate, PathConditions>
        ): PredicateState {
            val pathConditions = state.filter { it.type == PredicateType.Path() || it is CallPredicate && it != call }
            val inliner = CallExecutionConditionInliner(callPathConditions)
            return inliner.apply(pathConditions)
        }
    }
}

package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import org.jetbrains.research.kex.asm.analysis.refinements.MethodApproximationManager
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.model.TermDependency
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kfg.ir.Method

abstract class SingleCallResolver(
        val resolvingCall: CallPredicate,
        val currentCallContext: CallContext,
        val methodAnalyzer: MethodAnalyzer,
        val approximationManager: MethodApproximationManager
) {
    val resolvingCallTerm: CallTerm
        get() = resolvingCall.call as CallTerm

    val resolvingMethod: Method
        get() = resolvingCallTerm.method

    abstract fun resolve(
            state: PredicateStateWithPath,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>,
            tmpVariables: Set<Term>
    ): RecoveredModel

    companion object {
        private fun makeContext(base: CallContext, call: CallPredicate) =
                base.nested(call.memoryVersion)

        fun inline(
                base: CallContext,
                call: CallPredicate,
                methodAnalyzer: MethodAnalyzer,
                approximationManager: MethodApproximationManager
        ) = InlineCallResolver(call, makeContext(base, call), methodAnalyzer, approximationManager)

        fun open(
                base: CallContext,
                call: CallPredicate,
                methodAnalyzer: MethodAnalyzer,
                approximationManager: MethodApproximationManager
        ) = OpenCallResolver(call, makeContext(base, call), methodAnalyzer, approximationManager)

        fun empty(
                base: CallContext,
                call: CallPredicate,
                methodAnalyzer: MethodAnalyzer,
                approximationManager: MethodApproximationManager
        ) = EmptyCallResolver(call, makeContext(base, call), methodAnalyzer, approximationManager)
    }
}

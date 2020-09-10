package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import org.jetbrains.research.kex.asm.analysis.refinements.MethodApproximationManager
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.TermDependency
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.Term

abstract class SingleCallResolver(
        val currentCallContext: CallContext,
        val methodAnalyzer: MethodAnalyzer,
        val approximationManager: MethodApproximationManager
) {
    abstract fun resolve(
            state: PredicateStateWithPath,
            call: CallPredicate,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>, tmpVariables: Set<Term>
    ): RecoveredModel

    companion object {
        private fun makeContext(base: CallContext, call: CallPredicate) =
                base.nested(call.memoryVersion)

        fun inline(
                base: CallContext,
                call: CallPredicate,
                methodAnalyzer: MethodAnalyzer,
                approximationManager: MethodApproximationManager
        ) = InlineCallResolver(makeContext(base, call), methodAnalyzer, approximationManager)

        fun open(
                base: CallContext,
                call: CallPredicate,
                methodAnalyzer: MethodAnalyzer,
                approximationManager: MethodApproximationManager
        ) = OpenCallResolver(makeContext(base, call), methodAnalyzer, approximationManager)

        fun empty(
                base: CallContext,
                call: CallPredicate,
                methodAnalyzer: MethodAnalyzer,
                approximationManager: MethodApproximationManager
        ) = EmptyCallResolver(makeContext(base, call), methodAnalyzer, approximationManager)
    }
}

package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import org.jetbrains.research.kex.asm.analysis.refinements.MethodApproximationManager
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.TermDependency
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.Term

class EmptyCallResolver(
        currentCallContext: CallContext,
        methodAnalyzer: MethodAnalyzer,
        approximationManager: MethodApproximationManager
) : SingleCallResolver(currentCallContext, methodAnalyzer, approximationManager) {
    override fun resolve(
            state: PredicateStateWithPath,
            call: CallPredicate, dependencies: List<TermDependency>,
            pathVariables: Set<Term>, tmpVariables: Set<Term>
    ): RecoveredModel {
        TODO("No inline")
    }
}

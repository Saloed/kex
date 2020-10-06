package org.jetbrains.research.kex.refinements.analyzer.calls

import org.jetbrains.research.kex.refinements.MethodApproximationManager
import org.jetbrains.research.kex.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.model.TermDependency
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.Term

class EmptyCallResolver(
        resolvingCall: CallPredicate,
        currentCallContext: CallContext,
        methodAnalyzer: MethodAnalyzer,
        approximationManager: MethodApproximationManager
) : SingleCallResolver(resolvingCall, currentCallContext, methodAnalyzer, approximationManager) {
    override fun resolve(
            state: PredicateStateWithPath,
            dependencies: List<TermDependency>, pathVariables: Set<Term>,
            tmpVariables: Set<Term>
    ): RecoveredModel {
        TODO("No inline")
    }
}
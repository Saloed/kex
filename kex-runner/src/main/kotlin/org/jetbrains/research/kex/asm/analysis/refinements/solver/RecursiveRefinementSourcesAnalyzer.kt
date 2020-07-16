package org.jetbrains.research.kex.asm.analysis.refinements.solver

import org.jetbrains.research.kex.asm.analysis.refinements.*
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.FieldLoadTerm
import org.jetbrains.research.kfg.ir.Field

class RecursiveRefinementSourcesAnalyzer(methodAnalyzer: MethodAnalyzer) : RefinementSourcesAnalyzer(methodAnalyzer) {
    fun analyze(
            state: PredicateState,
            correctPath: PredicateState,
            sources: RefinementSources,
            recursiveRootCall: CallPredicate,
            recursiveCalls: Map<CallPredicate, Map<Field, FieldLoadTerm>>,
            recursivePaths: PredicateState
    ): Refinements {
        val refinements = sources.value.map {
            val refinement = querySolver(
                    query = { solver.analyzeRecursion(state, recursiveCalls, recursiveRootCall, recursivePaths, it.condition, correctPath) },
                    onError = { listOf(RecoveredModel.error()) }
            ).first().finalStateOrException()
            Refinement.create(it.criteria, refinement)
        }
        return createRefinements(refinements)
    }
}

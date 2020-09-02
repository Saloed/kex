package org.jetbrains.research.kex.asm.analysis.refinements.solver

import org.jetbrains.research.kex.asm.analysis.refinements.MethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.Refinement
import org.jetbrains.research.kex.asm.analysis.refinements.RefinementSources
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
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
        val refinements = sources.value.map { source ->
            val refinement = FixpointSolver(methodAnalyzer.cm)
                    .querySingle(
                            { analyzeRecursion(state, recursiveCalls, recursiveRootCall, recursivePaths, source.condition, correctPath) },
                            { RecoveredModel.error() }
                    ).finalStateOrException()
            Refinement.create(source.criteria, refinement)
        }
        return createRefinements(refinements)
    }
}

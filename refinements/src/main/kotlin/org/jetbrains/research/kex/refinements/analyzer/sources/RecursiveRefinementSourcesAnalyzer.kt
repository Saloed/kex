package org.jetbrains.research.kex.refinements.analyzer.sources

import org.jetbrains.research.kex.refinements.Refinement
import org.jetbrains.research.kex.refinements.RefinementSources
import org.jetbrains.research.kex.refinements.Refinements
import org.jetbrains.research.kex.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.refinements.solver.FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.query.RecursionFixpointSolverQuery
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
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
                            { query { RecursionFixpointSolverQuery(state, recursiveCalls, recursiveRootCall, recursivePaths, source.condition, correctPath) } },
                            { RecoveredModel.error() }
                    ).finalStateOrException()
            Refinement.create(source.criteria, refinement)
        }
        return createRefinements(refinements)
    }

    override fun queryRefinementSources(state: PredicateState, normals: PredicateState, sources: RefinementSources, memoryVersionInfo: MemoryVersionInfo): Refinements =
            error("Use analyze of recursive analyzer")
}

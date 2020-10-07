package org.jetbrains.research.kex.refinements.analyzer.sources

import org.jetbrains.research.kex.refinements.MethodApproximationManager
import org.jetbrains.research.kex.refinements.Refinement
import org.jetbrains.research.kex.refinements.RefinementSources
import org.jetbrains.research.kex.refinements.Refinements
import org.jetbrains.research.kex.refinements.analyzer.calls.CallResolver
import org.jetbrains.research.kex.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.refinements.solver.RefinementsSolverQuery
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector

open class CallResolvingRefinementSourcesAnalyzer(methodAnalyzer: MethodAnalyzer) : RefinementSourcesAnalyzer(methodAnalyzer) {
    override fun createRefinements(refinements: List<Refinement>): Refinements = when {
        refinements.any { !refinementIsCorrect(it) } -> error("Incorrect refinement")
        else -> super.createRefinements(refinements)
    }

    override fun queryRefinementSources(
            state: PredicateState,
            normals: PredicateState,
            sources: RefinementSources,
            memoryVersionInfo: MemoryVersionInfo
    ): Refinements {
        if (sources.value.isEmpty()) return Refinements.unknown(methodAnalyzer.method)
        MemoryUtils.verifyVersions(state)
        val solverQuery = RefinementsSolverQuery(state, normals, sources.value.map { it.condition }, emptySet(), memoryVersionInfo, 0)
        val callResolver = CallResolver(methodAnalyzer, methodsUnderApproximations)
        val result = callResolver.callResolutionLoop(solverQuery).map { it.finalStateOrException() }
        val refinements = sources.value.zip(result).map { (src, answer) -> Refinement.create(src.criteria, answer) }
        return Refinements.create(methodAnalyzer.method, refinements)
    }

    private fun refinementIsCorrect(refinement: Refinement): Boolean {
        if (PredicateCollector.collectIsInstance<CallPredicate>(refinement.state.state).isNotEmpty()) return false
        // todo: maybe more checks
        return true
    }

    companion object {
        val methodsUnderApproximations = MethodApproximationManager()
    }
}

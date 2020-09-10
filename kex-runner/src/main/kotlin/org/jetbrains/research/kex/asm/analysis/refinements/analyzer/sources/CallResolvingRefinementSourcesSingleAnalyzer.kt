package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.sources

import org.jetbrains.research.kex.asm.analysis.refinements.Refinement
import org.jetbrains.research.kex.asm.analysis.refinements.RefinementSources
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls.CallResolver
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.solver.RefinementsSolverQuery
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo

class CallResolvingRefinementSourcesSingleAnalyzer(methodAnalyzer: MethodAnalyzer) : CallResolvingRefinementSourcesAnalyzer(methodAnalyzer) {
    override fun queryRefinementSources(state: PredicateState, normals: PredicateState, sources: RefinementSources, memoryVersionInfo: MemoryVersionInfo): Refinements {
        if (sources.value.isEmpty()) return Refinements.unknown(methodAnalyzer.method)
        MemoryUtils.verifyVersions(state)
        val result = extendSourcesAndNormals(normals, sources).map { (extendedNormals, extendedSources) ->
            val solverQuery = RefinementsSolverQuery(state, extendedNormals, listOf(extendedSources), emptySet(), memoryVersionInfo, 0)
            val callResolver = CallResolver(methodAnalyzer, methodsUnderApproximations)
            callResolver.callResolutionLoop(solverQuery).map { it.finalStateOrException() }.first()
        }
        val refinements = sources.value.zip(result).map { (src, answer) -> Refinement.create(src.criteria, answer) }
        return Refinements.create(methodAnalyzer.method, refinements)
    }
}

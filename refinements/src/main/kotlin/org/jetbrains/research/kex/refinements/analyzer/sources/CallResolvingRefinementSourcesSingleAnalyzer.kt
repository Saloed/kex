package org.jetbrains.research.kex.refinements.analyzer.sources

import org.jetbrains.research.kex.refinements.Refinement
import org.jetbrains.research.kex.refinements.RefinementSources
import org.jetbrains.research.kex.refinements.Refinements
import org.jetbrains.research.kex.refinements.analyzer.calls.CallResolver
import org.jetbrains.research.kex.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.refinements.solver.RefinementsSolverQuery
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.not

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

    private fun extendSourcesAndNormals(normals: PredicateState, allSources: RefinementSources) = allSources.value.map { source ->
        val otherSources = allSources.value.filterNot { it == source }
                .map { it.condition }
                .let { ChoiceState(it) }
        val extendedNormals = ChoiceState(listOf(normals, otherSources))
        val extendedSource = ChainState(source.condition, otherSources.not())
        extendedNormals to extendedSource
    }
}

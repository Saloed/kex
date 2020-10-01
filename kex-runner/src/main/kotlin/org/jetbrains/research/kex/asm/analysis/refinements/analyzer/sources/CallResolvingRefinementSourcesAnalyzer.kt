package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.sources

import org.jetbrains.research.kex.asm.analysis.refinements.MethodApproximationManager
import org.jetbrains.research.kex.asm.analysis.refinements.Refinement
import org.jetbrains.research.kex.asm.analysis.refinements.RefinementSources
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls.CallResolver
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.solver.RefinementsSolverQuery
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.not
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector

open class CallResolvingRefinementSourcesAnalyzer(methodAnalyzer: MethodAnalyzer) : RefinementSourcesAnalyzer(methodAnalyzer) {
    override fun createRefinements(refinements: List<Refinement>): Refinements = when {
        refinements.any { !refinementIsCorrect(it) } -> error("Incorrect refinement")
        else -> super.createRefinements(refinements)
    }

    override fun queryRefinementSources(state: PredicateState, normals: PredicateState, sources: RefinementSources, memoryVersionInfo: MemoryVersionInfo): Refinements {
        if (sources.value.isEmpty()) return Refinements.unknown(methodAnalyzer.method)
        MemoryUtils.verifyVersions(state)
        val (_, extendedSources) = extendSourcesAndNormals(normals, sources).unzip()
        val solverQuery = RefinementsSolverQuery(state, normals, extendedSources, emptySet(), memoryVersionInfo, 0)
        val callResolver = CallResolver(methodAnalyzer, methodsUnderApproximations)
        val result = callResolver.callResolutionLoop(solverQuery).map { it.finalStateOrException() }
        val refinements = sources.value.zip(result).map { (src, answer) -> Refinement.create(src.criteria, answer) }
        return Refinements.create(methodAnalyzer.method, refinements)
    }

    fun extendSourcesAndNormals(normals: PredicateState, allSources: RefinementSources) = allSources.value.map { source ->
        val otherSources = allSources.value.filterNot { it == source }
                .map { it.condition }
                .let { ChoiceState(it) }
        val extendedNormals = ChoiceState(listOf(normals, otherSources))
        val extendedSource = ChainState(source.condition, otherSources.not())
        extendedNormals to extendedSource
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

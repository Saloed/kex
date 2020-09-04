package org.jetbrains.research.kex.asm.analysis.refinements.solver

import org.jetbrains.research.kex.asm.analysis.refinements.*
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.not
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector

class CallResolvingRefinementSourcesAnalyzer(methodAnalyzer: MethodAnalyzer) : RefinementSourcesAnalyzer(methodAnalyzer) {
    override fun createRefinements(refinements: List<Refinement>): Refinements = when {
        refinements.any { !refinementIsCorrect(it) } -> throw IllegalStateException("Incorrect refinement")
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

    private fun extendSourcesAndNormals(normals: PredicateState, allSources: RefinementSources) = allSources.value.map { source ->
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
        private val methodsUnderApproximations = MethodApproximationManager()
    }
}
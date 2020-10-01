package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.sources

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.refinements.Refinement
import org.jetbrains.research.kex.asm.analysis.refinements.RefinementSource
import org.jetbrains.research.kex.asm.analysis.refinements.RefinementSources
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer.Companion.applyAdapters
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.transformer.transform

abstract class RefinementSourcesAnalyzer(val methodAnalyzer: MethodAnalyzer) {
    fun analyze(state: PredicateState, correctPath: PredicateState, sources: RefinementSources, memoryVersionInfo: MemoryVersionInfo): Refinements {
        val (trivialRefinements, sourcesToQuery) = searchForDummySolution(correctPath, sources)
        val otherRefinements = queryRefinementSources(state, correctPath, sourcesToQuery, memoryVersionInfo)
        return createRefinements(trivialRefinements.value + otherRefinements.value)
    }

    abstract fun queryRefinementSources(state: PredicateState, normals: PredicateState, sources: RefinementSources, memoryVersionInfo: MemoryVersionInfo): Refinements

    open fun createRefinements(refinements: List<Refinement>): Refinements =
            Refinements.create(methodAnalyzer.method, refinements)
                    .fmap {
                        val state = transform(it.state) { applyAdapters(methodAnalyzer) }
                        val path = transform(it.path) { applyAdapters(methodAnalyzer) }
                        PredicateStateWithPath(state, path)
                    }

    private fun searchForDummySolution(normals: PredicateState, exceptions: RefinementSources): Pair<Refinements, RefinementSources> {
        val sourcesToQuery = mutableListOf<RefinementSource>()
        val dummyRefinements = mutableListOf<Refinement>()
        for (source in exceptions.value) {
            val dummyResult = analyzeForDummyResult(normals, source.condition)
            if (dummyResult == null) {
                sourcesToQuery.add(source)
                continue
            }
            dummyRefinements.add(Refinement.create(source.criteria, dummyResult))
        }
        return Refinements.create(methodAnalyzer.method, dummyRefinements) to RefinementSources.create(sourcesToQuery)
    }

    private fun analyzeForDummyResult(normalPaths: PredicateState, exceptionPaths: PredicateState): PredicateStateWithPath? = when {
        normalPaths.evaluatesToTrue && exceptionPaths.evaluatesToFalse -> PredicateStateWithPath(emptyState(), falseState())
        normalPaths.evaluatesToFalse && exceptionPaths.evaluatesToTrue -> PredicateStateWithPath(emptyState(), trueState())
        normalPaths.evaluatesToTrue && exceptionPaths.evaluatesToTrue -> {
            log.error("Normal and Exception paths are always true")
            PredicateStateWithPath(emptyState(), falseState())
        }
        normalPaths.evaluatesToFalse && exceptionPaths.evaluatesToFalse -> {
            log.error("Normal and Exception paths are always false")
            PredicateStateWithPath(emptyState(), falseState())
        }
        else -> null
    }
}

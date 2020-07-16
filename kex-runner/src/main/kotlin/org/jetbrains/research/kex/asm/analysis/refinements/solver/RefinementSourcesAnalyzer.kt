package org.jetbrains.research.kex.asm.analysis.refinements.solver

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.refinements.*
import org.jetbrains.research.kex.asm.analysis.refinements.MethodAnalyzer.Companion.applyAdapters
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.transformer.transform
import org.jetbrains.research.kex.state.trueState

open class RefinementSourcesAnalyzer(val methodAnalyzer: MethodAnalyzer) {

    val solver: Z3FixpointSolver
        get() = Z3FixpointSolver(methodAnalyzer.cm.type)

    fun analyze(state: PredicateState, correctPath: PredicateState, sources: RefinementSources): Refinements {
        val (trivialRefinements, sourcesToQuery) = searchForDummySolution(correctPath, sources)
        val otherRefinements = queryRefinementSources(state, correctPath, sourcesToQuery)
        return createRefinements(trivialRefinements.value + otherRefinements.value)
    }

    open fun createRefinements(refinements: List<Refinement>): Refinements =
            Refinements.create(methodAnalyzer.method, refinements)
                    .fmap { transform(it) { applyAdapters(methodAnalyzer) } }

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

    private fun analyzeForDummyResult(normalPaths: PredicateState, exceptionPaths: PredicateState): PredicateState? = when {
        normalPaths.evaluatesToTrue && exceptionPaths.evaluatesToFalse -> falseState()
        normalPaths.evaluatesToFalse && exceptionPaths.evaluatesToTrue -> trueState()
        normalPaths.evaluatesToTrue && exceptionPaths.evaluatesToTrue -> {
            log.error("Normal and Exception paths are always true")
            falseState()
        }
        normalPaths.evaluatesToFalse && exceptionPaths.evaluatesToFalse -> {
            log.error("Normal and Exception paths are always false")
            falseState()
        }
        else -> null
    }

    open fun queryRefinementSources(state: PredicateState, normals: PredicateState, sources: RefinementSources): Refinements {
        if (sources.value.isEmpty()) return Refinements.unknown(methodAnalyzer.method)
        val conditions = sources.value.map { it.condition }
        val fixpointAnswer = queryFixpointSolver(state, normals, conditions).map { it.finalStateOrException() }
        val refinements = sources.value.zip(fixpointAnswer).map { (src, answer) -> Refinement.create(src.criteria, answer) }
        return Refinements.create(methodAnalyzer.method, refinements)
    }

    private fun queryFixpointSolver(state: PredicateState, normal: PredicateState, exceptions: List<PredicateState>): List<RecoveredModel> =
            querySolver(
                    query = { solver.mkFixpointQuery(state, exceptions, normal) },
                    onError = { exceptions.map { RecoveredModel.error() } }
            )

    inline fun querySolver(query: () -> FixpointResult, onError: () -> List<RecoveredModel>): List<RecoveredModel> =
            try {
                val result = query()
                when (result) {
                    is FixpointResult.Sat -> result.result
                    is FixpointResult.Unknown -> {
                        log.error("Unknown: ${result.reason}")
                        onError()
                    }
                    is FixpointResult.Unsat -> {
                        log.error("Unsat: ${result.core.contentToString()}")
                        onError()
                    }
                }
            } catch (ex: QueryCheckStatus.FixpointQueryException) {
                log.error("Bad fixpoint query: ${ex.status}")
                onError()
            }
}
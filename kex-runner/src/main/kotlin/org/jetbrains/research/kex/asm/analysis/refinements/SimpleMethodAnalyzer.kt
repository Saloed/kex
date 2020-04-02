package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kex.state.trueState
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method

class SimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method): MethodAnalyzer(cm, psa, mr, method) {

    override fun analyze(): Refinements {
        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, method)
        val state = methodPaths.fullState
        val refinementSources = methodPaths.refinementSources
        val normalPaths = methodPaths.normalExecutionPaths
        val (nestedNormal, nestedRefinementSources) = inlineRefinements()

        val allSources = refinementSources.merge(nestedRefinementSources)
        val allNormal = ChainState(normalPaths, nestedNormal).optimize()

        log.info("Analyze: $method")
        log.info("State:\n$state\nExceptions:\n$allSources\nNormal:\n$allNormal")

        val (trivialRefinements, sourcesToQuery) = searchForDummySolution(allNormal, allSources)
        val otherRefinements = queryRefinementSources(state, allNormal, sourcesToQuery)

        return Refinements(trivialRefinements.value + otherRefinements.value, method)
    }

    private fun searchForDummySolution(normal: PredicateState, exceptions: RefinementSources): Pair<Refinements, RefinementSources> {
        val sourcesToQuery = mutableListOf<RefinementSource>()
        val dummyRefinements = mutableListOf<Refinement>()
        for (source in exceptions.value) {
            val dummyResult = analyzeForDummyResult(normal, source.condition)
            if (dummyResult == null) {
                sourcesToQuery.add(source)
                continue
            }
            dummyRefinements.add(Refinement.create(source.criteria, dummyResult))
        }
        return Refinements(dummyRefinements, method) to RefinementSources(sourcesToQuery)
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

    private fun queryRefinementSources(state: PredicateState, normal: PredicateState, sources: RefinementSources): Refinements {
        if (sources.value.isEmpty()) return Refinements(emptyList(), method)
        val conditions = sources.value.map { it.condition }
        val fixpointAnswer = queryFixpointSolver(state, normal, conditions)
        val refinements = sources.value.zip(fixpointAnswer).map { (src, answer) -> Refinement.create(src.criteria, answer) }
        return Refinements(refinements, method)
    }

    private fun queryFixpointSolver(state: PredicateState, normal: PredicateState, exceptions: List<PredicateState>): List<PredicateState> =
            try {
                val result = Z3FixpointSolver(cm.type).mkFixpointQuery(state, exceptions, normal)
                when (result) {
                    is FixpointResult.Sat -> result.result
                    else -> {
                        if (result is FixpointResult.Unknown) log.error("Unknown: ${result.reason}")
                        exceptions.map { falseState() }
                    }
                }
            } catch (ex: QueryCheckStatus.FixpointQueryException) {
                log.error("Bad fixpoint query: ${ex.status}")
                exceptions.map { falseState() }
            }
}
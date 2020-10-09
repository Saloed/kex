package org.jetbrains.research.kex.refinements.analyzer.method

import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.refinements.MethodApproximationManager
import org.jetbrains.research.kex.refinements.Refinements
import org.jetbrains.research.kex.refinements.analyzer.exceptions.ExceptionSource
import org.jetbrains.research.kex.refinements.analyzer.exceptions.RefinementSourceBuilder
import org.jetbrains.research.kex.refinements.analyzer.utils.MethodExecutionPathsAnalyzer
import org.jetbrains.research.kex.refinements.analyzer.utils.RecursiveCallsAnalyzer
import org.jetbrains.research.kex.refinements.solver.FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.query.NewRecursiveFixpointQuery
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method

class NewRecursiveMethodAnalyzer(
        cm: ClassManager,
        psa: PredicateStateAnalysis,
        mr: MethodRefinements,
        method: Method
) : MethodAnalyzer(cm, psa, mr, method) {
    override fun analyze(): Refinements {
        val recursiveCallTraces = RecursiveCallsAnalyzer(refinementsManager, cm, method).analyze(method)
        check(recursiveCallTraces.isNotEmpty()) { "No recursive calls at analysis of recursive method" }
        check(RecursiveCallsAnalyzer.allRecursiveCallsPlacedInMethodBody(recursiveCallTraces)) { "Non direct recursive calls are not supported" }
        val recursiveCallInstructions = RecursiveCallsAnalyzer.recursiveCallInstructions(recursiveCallTraces)
                .map { it.first }.toSet()

        val methodPaths = MethodExecutionPathsAnalyzer(cm, psa, method)
        val (statePrepared, callPathConditions) = inlineCalls(methodPaths.methodRawFullState(), ignore = recursiveCallInstructions)
        val (state, memoryVersionInfo) = buildMemoryVersions(statePrepared)

        val throwSources = methodPaths.throws.map { ExceptionSource.MethodException(it) }
        val callSources = callPathConditions.map { (call, pc) -> ExceptionSource.CallException(call, pc) }
        val allCriteria = (throwSources + callSources).flatMap { it.criteria() }.toSet()
        val recursiveSources = recursiveCallInstructions.map { ExceptionSource.RecursiveCallException(it, allCriteria) }
        val sourceBuilder = RefinementSourceBuilder(method, throwSources + callSources + recursiveSources)
        val allSources = sourceBuilder.buildExceptionSources()
        val allNormal = sourceBuilder.buildNormals(methodPaths.returns)

        val approximationManager = MethodApproximationManager()
        val stateWithApproximations = approximationManager.extendWithUnderApproximations(state)
        val (correctedStateWithApproximations, correctedMemoryVersionInfo) = approximationManager.correctMemoryAfterApproximation(stateWithApproximations, memoryVersionInfo)

        val recursiveCallPredicates = PredicateCollector.collectIsInstance<CallPredicate>(correctedStateWithApproximations)
                .filter { it.callTerm.instruction in recursiveCallInstructions }
                .toSet()

        check(allSources.value.size == 1) { "TODO: sources" }

        val singleRefinementSource = allSources.value.first()
        val solver = FixpointSolver(cm)
        val result = solver.querySingle {
            query {
                NewRecursiveFixpointQuery(
                        correctedStateWithApproximations,
                        singleRefinementSource.condition,
                        allNormal,
                        correctedMemoryVersionInfo,
                        recursiveCallPredicates
                )
            }
        }

        return Refinements.unknown(method)
    }

}

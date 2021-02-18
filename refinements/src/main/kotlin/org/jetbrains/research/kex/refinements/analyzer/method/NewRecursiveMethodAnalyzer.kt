package org.jetbrains.research.kex.refinements.analyzer.method

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.refinements.*
import org.jetbrains.research.kex.refinements.analyzer.calls.CallResolver
import org.jetbrains.research.kex.refinements.analyzer.exceptions.ExceptionSource
import org.jetbrains.research.kex.refinements.analyzer.exceptions.RefinementSourceBuilder
import org.jetbrains.research.kex.refinements.analyzer.utils.MethodExecutionPathsAnalyzer
import org.jetbrains.research.kex.refinements.analyzer.utils.RecursiveCallsAnalyzer
import org.jetbrains.research.kex.refinements.solver.FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.query.NewRecursiveFixpointQuery
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.not
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kex.util.structuralMatch
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst

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
        val (statePrepared, callPathConditions) = inlineCalls(
            methodPaths.methodRawFullState(),
            ignore = recursiveCallInstructions
        )
        val (state, memoryVersionInfo) = buildMemoryVersions(statePrepared)

        val (allSources, allNormal, initial) = getMethodPaths(methodPaths, callPathConditions, recursiveCallInstructions)

        val approximationManager = MethodApproximationManager()
        val stateWithApproximations = approximationManager.extendWithUnderApproximations(state)
        val (correctedStateWithApproximations, correctedMemoryVersionInfo) = approximationManager.correctMemoryAfterApproximation(
            stateWithApproximations,
            memoryVersionInfo
        )

        val recursiveCallPredicates =
            PredicateCollector.collectIsInstance<CallPredicate>(correctedStateWithApproximations)
                .filter { it.callTerm.instruction in recursiveCallInstructions }
                .toSet()

        check(allSources.value.size == 1) { "TODO: sources" }

        log.debug("State:\n$correctedStateWithApproximations\nSources:\n$allSources\nNormals:\n$allNormal")

        val singleRefinementSource = allSources.value.first()
        val solver = FixpointSolver(cm)
        val result = solver.querySingle {
            query {
                NewRecursiveFixpointQuery(
                    correctedStateWithApproximations,
                    initial,
                    allNormal,
                    singleRefinementSource.condition,
                    correctedMemoryVersionInfo,
                    recursiveCallPredicates,
                    this@NewRecursiveMethodAnalyzer::resolveExternalCall
                )
            }
        }
        val finalResult = result.finalStateOrException()
        val refinement = Refinement.create(singleRefinementSource.criteria, finalResult)
        return Refinements.create(method, listOf(refinement))
    }

    private fun getMethodPaths(
        methodPaths: MethodExecutionPathsAnalyzer,
        callPathConditions: Map<CallPredicate, PathConditions>,
        recursiveCallInstructions: Set<CallInst>
    ): Triple<RefinementSources, PredicateState, PredicateState> {
        val throwSources = methodPaths.throws.map { ExceptionSource.MethodException(it) }
        val callSources = callPathConditions.map { (call, pc) -> ExceptionSource.CallException(call, pc) }
        val allCriteria = (throwSources + callSources).flatMap { it.criteria() }.toSet()
        val recursiveNormalSources = recursiveCallInstructions.map { ExceptionSource.RecursiveCallException(it, allCriteria, callIsException = false) }
        val recursiveExceptionSources = recursiveCallInstructions.map { ExceptionSource.RecursiveCallException(it, allCriteria, callIsException = true) }
        val normalSourceBuilder = RefinementSourceBuilder(method, throwSources + callSources + recursiveNormalSources)
        val exSourceBuilder = RefinementSourceBuilder(method, throwSources + callSources + recursiveExceptionSources)

        val exceptionSourceWithNoRecursiveCall = normalSourceBuilder.buildExceptionSources()
        val allExceptionSources = exSourceBuilder.buildExceptionSources()
        val normalWithNoRecursiveCall = exSourceBuilder.buildNormals(methodPaths.returns)
        val allNormals = normalSourceBuilder.buildNormals(methodPaths.returns)
        val onlyRecursiveCallsAsExceptionSources = allExceptionSources.merge(exceptionSourceWithNoRecursiveCall) { allCond, nonRecCond ->
            ChainState(allCond, nonRecCond.not())
        }.fmap { it.optimize() }
        val onlyRecursiveCallsAsNormal = ChainState(allNormals, normalWithNoRecursiveCall.not()).optimize()

        return Triple(exceptionSourceWithNoRecursiveCall, onlyRecursiveCallsAsNormal, normalWithNoRecursiveCall)
    }

    private fun resolveExternalCall(model: RecoveredModel): PredicateStateWithPath? {
        log.debug("Run solver for external call")
        val methodsUnderApproximations = MethodApproximationManager()
        val callResolver = CallResolver(this, methodsUnderApproximations)
        callResolver.resolveCalls(model)

        val minedApproximations = methodsUnderApproximations.underApproximations
        check(minedApproximations.size == 1) { "Single call expected" }
        val (_, approximations) = minedApproximations.entries.first()
        val queryApprox = approximations.approximations
        check(queryApprox.size == 1) { "To many approximations" }
        val queryResult = queryApprox.first()
        check(structuralMatch(queryResult.post, model.state)) { "Query structure mismatch" }
        return queryResult.pre
    }


}

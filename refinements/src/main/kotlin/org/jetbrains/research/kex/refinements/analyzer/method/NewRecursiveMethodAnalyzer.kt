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
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kex.state.transformer.TermRemapper
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

        val executionPaths = getMethodPaths(methodPaths, callPathConditions, recursiveCallInstructions)

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

        check(executionPaths.exceptionSourceWithNoRecursiveCall.value.size == 1) { "TODO: sources" }

        log.debug("State:\n$correctedStateWithApproximations\nSources:\n${executionPaths.allExceptionSources}\nNormals:\n${executionPaths.allNormals}")

        val normalExecutionConditions = queryNormalExecutionConditions(
            executionPaths,
            correctedStateWithApproximations,
            correctedMemoryVersionInfo,
            recursiveCallPredicates
        )
        val exceptionalExecutionConditions = queryExceptionalExecutionConditions(
            executionPaths,
            correctedStateWithApproximations,
            correctedMemoryVersionInfo,
            recursiveCallPredicates,
            normalExecutionConditions
        )
        log.debug("Result:\n$exceptionalExecutionConditions")
        return exceptionalExecutionConditions
    }

    private fun queryExceptionalExecutionConditions(
        executionPaths: ExecutionPaths,
        state: PredicateState,
        memoryVersions: MemoryVersionInfo,
        recursiveCallPredicates: Set<CallPredicate>,
        normalExecutionConditions: Refinements
    ): Refinements {
        val singleRefinementSource = executionPaths.allExceptionSources.value.first()
        val normalExecutionCondition = normalExecutionConditions.value.first()
        check(singleRefinementSource.criteria == normalExecutionCondition.criteria) { "Criteria mismatch" }
        val solver = FixpointSolver(cm)
        val result = solver.querySingle {
            query {
                NewRecursiveFixpointQuery(
                    state,
                    normalExecutionCondition.state.negate().toPredicateState(),
                    singleRefinementSource.condition,
                    executionPaths.allNormals,
                    memoryVersions,
                    recursiveCallPredicates,
                    this@NewRecursiveMethodAnalyzer::resolveExternalCall
                )
            }
        }
        val finalResult = result.finalStateOrException()
        val refinement = Refinement.create(singleRefinementSource.criteria, finalResult)
        return Refinements.create(method, listOf(refinement))
    }

    private fun queryNormalExecutionConditions(
        executionPaths: ExecutionPaths,
        state: PredicateState,
        memoryVerions: MemoryVersionInfo,
        recursiveCallPredicates: Set<CallPredicate>
    ): Refinements {
        val singleRefinementSource = executionPaths.exceptionSourceWithNoRecursiveCall.value.first()
        val solver = FixpointSolver(cm)
        val result = solver.querySingle {
            query {
                NewRecursiveFixpointQuery(
                    state,
                    executionPaths.normalWithNoRecursiveCall,
                    executionPaths.onlyRecursiveCallsAsNormal,
                    singleRefinementSource.condition,
                    memoryVerions,
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
    ): ExecutionPaths {
        val throwSources = methodPaths.throws.map { ExceptionSource.MethodException(it) }
        val callSources = callPathConditions.map { (call, pc) -> ExceptionSource.CallException(call, pc) }
        val allCriteria = (throwSources + callSources).flatMap { it.criteria() }.toSet()
        val recursiveNormalSources = recursiveCallInstructions.map {
            ExceptionSource.RecursiveCallException(it, allCriteria, callIsException = false)
        }
        val recursiveExceptionSources = recursiveCallInstructions.map {
            ExceptionSource.RecursiveCallException(it, allCriteria, callIsException = true)
        }
        val normalSourceBuilder = RefinementSourceBuilder(method, throwSources + callSources + recursiveNormalSources)
        val exSourceBuilder = RefinementSourceBuilder(method, throwSources + callSources + recursiveExceptionSources)

        val exceptionSourceWithNoRecursiveCall = normalSourceBuilder.buildExceptionSources()
        val allExceptionSources = exSourceBuilder.buildExceptionSources()
        val normalWithNoRecursiveCall = exSourceBuilder.buildNormals(methodPaths.returns)
        val allNormals = normalSourceBuilder.buildNormals(methodPaths.returns)
        val onlyRecursiveCallsAsExceptionSources =
            allExceptionSources.merge(exceptionSourceWithNoRecursiveCall) { allCond, nonRecCond ->
                ChainState(allCond, nonRecCond.not())
            }.fmap { it.optimize() }
        val onlyRecursiveCallsAsNormal = ChainState(allNormals, normalWithNoRecursiveCall.not()).optimize()

        return ExecutionPaths(
            exceptionSourceWithNoRecursiveCall,
            onlyRecursiveCallsAsExceptionSources,
            allExceptionSources,
            normalWithNoRecursiveCall,
            onlyRecursiveCallsAsNormal,
            allNormals
        )
    }

    private fun resolveExternalCall(model: RecoveredModel): PredicateState {
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
        return inlinePathVariables(queryResult.pre)
    }

    private data class ExecutionPaths(
        val exceptionSourceWithNoRecursiveCall: RefinementSources,
        val onlyRecursiveCallsAsExceptionSources: RefinementSources,
        val allExceptionSources: RefinementSources,
        val normalWithNoRecursiveCall: PredicateState,
        val onlyRecursiveCallsAsNormal: PredicateState,
        val allNormals: PredicateState
    )


    private fun inlinePathVariables(predicateStateWithPath: PredicateStateWithPath): PredicateState {
        val bindings = pathVariablesBindings(predicateStateWithPath.state)
        return TermRemapper(bindings).apply(predicateStateWithPath.path)
    }

    private fun pathVariablesBindings(state: PredicateState): Map<Term, Term> = when (state) {
        is BasicState -> state.predicates.map {
            val binding = (it as? EqualityPredicate) ?: error("Unexpected predicate $it")
            binding.lhv to binding.rhv
        }.toMap()
        is ChainState -> pathVariablesBindings(state.base) + pathVariablesBindings(state.curr)
        else -> error("Unexpected state: $state")
    }

}

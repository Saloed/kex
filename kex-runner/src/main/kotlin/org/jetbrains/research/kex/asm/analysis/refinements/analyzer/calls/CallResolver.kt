package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.refinements.MethodApproximationManager
import org.jetbrains.research.kex.asm.analysis.refinements.MethodUnderApproximation
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.solver.FixpointSolver
import org.jetbrains.research.kex.asm.analysis.refinements.solver.SolverQuery
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.TermDependency
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.memory.MemoryAccess
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.ConstBoolTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.*
import kotlin.math.absoluteValue

class CallResolver(
        val methodAnalyzer: MethodAnalyzer,
        val approximationManager: MethodApproximationManager,
        private val callContext: CallContext = CallContext.ROOT
) {
    inline fun <reified T : SolverQuery<T, List<RecoveredModel>>> callResolutionLoop(query: T): List<RecoveredModel> {
        while (true) {
            log.debug("Enter ${query.iteration} call resolution loop for ${methodAnalyzer.method}")
            val processed = query.updateIteration { it.inc() }
                    .transform { approximationManager.extendWithUnderApproximations(it) }
                    .updateIgnoredCalls { ignoreCalls(query, it) }
                    .acceptMemoryCorrector { ps, versionInfo ->
                        approximationManager.correctMemoryAfterApproximation(ps, versionInfo)
                    }
                    .run(FixpointSolver(methodAnalyzer.cm))
            when {
                processed.all { it.isFinal } -> return processed
                else -> processed.forEach { resolveCalls(it) }
            }
        }
    }

    fun <T : SolverQuery<T, List<RecoveredModel>>> ignoreCalls(query: T, ignored: Set<CallPredicate>): Set<CallPredicate> {
        val callCollector = PredicateCollector { it is CallPredicate }
        query.transform { callCollector.transform(it); it }
        val allCalls = callCollector.predicates.filterIsInstance<CallPredicate>().toSet()
        val callsToCheck = allCalls - ignored
        val callsToIgnore = callsToCheck.filter { callMayBeIgnored(it) }
        return ignored + callsToIgnore
    }

    private fun callMayBeIgnored(call: CallPredicate): Boolean {
        val approximation = approximationManager.underApproximations[call] ?: return false
        return approximation.approximations.isNotEmpty()
    }

    fun resolveCalls(model: RecoveredModel) {
        val splitted = splitModel(model)
        splitted.forEach { resolveCallsInSplitModel(it) }
    }

    private fun resolveCallsInSplitModel(model: RecoveredModel){
        if (model.isFinal) return
        val calls = model.dependencies.groupBy { it.call }
        if (calls.isEmpty()) return
        if (calls.size > 1) return tryResolveMultipleCalls(model)
        val (call, dependencies) = calls.entries.last()
        resolveSingleCall(model.state, call, dependencies, model.pathVariables, model.tmpVariables)
    }

    private fun tryResolveMultipleCalls(model: RecoveredModel) {
//        val singleDepsPredicates = collectPredicatesWithSingleDependentTerm(model.state, model.dependencies)
        when {
//            singleDepsPredicates.isNotEmpty() -> singleDepsPredicates.forEach { (predicate, callIdx) ->
//                val depsToResolve = model.dependencies.filter { it.callIdx == callIdx }
//                val callToResolve = depsToResolve.first().call
//                resolveSingleCall(predicate.wrap(), callToResolve, depsToResolve, model.pathVariables, model.tmpVariables)
//            }
            else -> {
                val maxId = model.dependencies.map { it.callIdx }.maxOrNull() ?: error("impossible")
                val depsToResolve = model.dependencies.filter { it.callIdx == maxId }
                val callToResolve = depsToResolve.first().call
                resolveSingleCall(model.state, callToResolve, depsToResolve, model.pathVariables, model.tmpVariables)
            }
        }
    }

    private fun splitModel(model: RecoveredModel): List<RecoveredModel> {
        val (state, path) = model.state
        val aliasAnalysis = StensgaardAA().apply { apply(state) }
        val slicedStates = PredicateCollector.collectIsInstance<EqualityPredicate>(path)
                .groupBy({ it.lhv }, { it.rhv })
                .mapValues { (_, values) -> values.filterIsInstance<ConstBoolTerm>().map { it.value }.distinct() }
                .mapValues { (pv, conditionValues) ->
                    val slicedState = Slicer(state, setOf(pv), aliasAnalysis).apply(state)
                    val conditions = conditionValues.map { basic { path { pv equality it } } }
                    conditions.map { slicedState to it }
                }
                .flatMap { (_, stateWithConds) -> stateWithConds }
                .map { (state, condition) -> PredicateStateWithPath(state, condition) }
        return slicedStates.map { it.asModelWithRelatedDependencies(model) }
    }

    private fun PredicateStateWithPath.asModelWithRelatedDependencies(model: RecoveredModel): RecoveredModel {
        val memoryAccess = MemoryUtils.collectMemoryAccesses(state).toSet()
        val stateTerms = TermCollector.getFullTermSet(state)
        val pathTerms = TermCollector.getFullTermSet(path)

        val memoryDependencies = model.dependencies
                .filterIsInstance<TermDependency.MemoryDependency>()
                .filter { it.memoryAccess in memoryAccess }
        val callResultDependencies = model.dependencies
                .filterIsInstance<TermDependency.CallResultDependency>()
                .filter { it.term in stateTerms || it.term in pathTerms }
        val dependencies = memoryDependencies + callResultDependencies
        val tmpVariables = model.tmpVariables.filter { it in stateTerms || it in pathTerms }.toSet()
        val pathVariables = model.pathVariables.filter { it in stateTerms || it in pathTerms }.toSet()
        return RecoveredModel(this, dependencies.toSet(), pathVariables, tmpVariables)
    }

    private fun collectPredicatesWithSingleDependentTerm(state: PredicateState, dependencies: Set<TermDependency>): List<Pair<Predicate, Int>> {
        val memoryDependency = dependencies.filterIsInstance<TermDependency.MemoryDependency>().associateBy { it.memoryAccess }
        val callResultDependency = dependencies.filterIsInstance<TermDependency.CallResultDependency>().associateBy { it.term }
        val result = mutableListOf<Pair<Predicate, Int>>()
        PredicateCollector.collectIsInstance<Predicate>(state).forEach { predicate ->
            val dependentTerms = TermCollector.getFullTermSet(predicate).mapNotNull {
                when (it) {
                    is MemoryAccess<*> -> memoryDependency[it]?.callIdx
                    else -> callResultDependency[it]?.callIdx
                }
            }.distinct()
            when {
                predicate is MemoryAccess<*> && dependentTerms.isEmpty() -> {
                    val dependency = memoryDependency[predicate]
                    if (dependency != null) {
                        result += predicate to dependency.callIdx
                    }
                }
                predicate !is MemoryAccess<*> && dependentTerms.size == 1 -> {
                    val dependency = dependentTerms.first()
                    result += predicate to dependency
                }
            }
        }
        return result
    }

    private fun resolveSingleCall(
            state: PredicateStateWithPath,
            call: CallPredicate,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>, tmpVariables: Set<Term>
    ) {
        val inlineStatus = MethodManager.InlineManager.isInlinable((call.call as CallTerm).method)
        val resolver = when (inlineStatus) {
            MethodManager.InlineManager.InlineStatus.INLINE -> SingleCallResolver.inline(callContext, call, methodAnalyzer, approximationManager)
            MethodManager.InlineManager.InlineStatus.MAY_INLINE -> SingleCallResolver.open(callContext, call, methodAnalyzer, approximationManager)
            MethodManager.InlineManager.InlineStatus.NO_INLINE -> SingleCallResolver.empty(callContext, call, methodAnalyzer, approximationManager)
        }
        val callPreconditions = resolver.resolve(state, call, dependencies, pathVariables, tmpVariables)
        val renamedCallPreconditions = renameStateVariables(callPreconditions.state, callPreconditions.pathVariables, callPreconditions.tmpVariables, call, "pre")
        val renamedCallPostConditions = renameStateVariables(state, pathVariables, tmpVariables, call, "post")
        approximationManager.update(call, MethodUnderApproximation(renamedCallPreconditions, renamedCallPostConditions))
    }

    private fun renameStateVariables(
            state: PredicateStateWithPath,
            pathVariables: Set<Term>, tmpVariables: Set<Term>,
            call: CallPredicate,
            prefix: String
    ): PredicateStateWithPath {
        val rootVariableGenerator = callContext.variableGenerator.createNestedGenerator("${call.hashCode().absoluteValue}")
        val tmpVariableGenerator = rootVariableGenerator.createNestedGenerator(prefix).createNestedGenerator("tmp")
        val pathVariableGenerator = rootVariableGenerator.createNestedGenerator(prefix).createNestedGenerator("path")
        val tmpMapping = tmpVariables.associateWith { tmpVariableGenerator.generatorFor(it).createVar(it.type) }
        val pathMapping = pathVariables.associateWith { pathVariableGenerator.generatorFor(it).createVar(it.type) }
        val termMapper = TermRemapper(tmpMapping + pathMapping)
        return state.accept(termMapper::apply)
    }
}

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
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kex.state.transformer.TermRemapper
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
//            log.debug("Resolved ${query.iteration} call resolution loop for ${methodAnalyzer.method}\n$processed")
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
        if (model.isFinal) return
        val calls = model.dependencies.groupBy { it.call }
        if (calls.isEmpty()) return
        if (calls.size > 1) return tryResolveMultipleCalls(model)
        val (call, dependencies) = calls.entries.last()
        resolveSingleCall(model.state, call, dependencies, model.pathVariables, model.tmpVariables)
    }

    private fun tryResolveMultipleCalls(model: RecoveredModel) {
        val maxId = model.dependencies.map { it.callIdx }.maxOrNull() ?: error("impossible")
        val depsToResolve = model.dependencies.filter { it.callIdx == maxId }
        val callToResolve = depsToResolve.first().call
        resolveSingleCall(model.state, callToResolve, depsToResolve, model.pathVariables, model.tmpVariables)
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
        val callPreconditions = resolver.resolve(state, dependencies, pathVariables, tmpVariables)
        val renamedCallPreconditions = renameStateVariables(callPreconditions.state, callPreconditions.pathVariables, callPreconditions.tmpVariables, call, "pre")
        val renamedCallPostConditions = renameStateVariables(state, pathVariables, tmpVariables, call, "post")
        saveApproximation(call, renamedCallPreconditions, renamedCallPostConditions)
    }

    private fun saveApproximation(call: CallPredicate, renamedCallPreconditions: PredicateStateWithPath, renamedCallPostConditions: PredicateStateWithPath) {
        val approximation = MethodUnderApproximation(renamedCallPreconditions, renamedCallPostConditions)
        log.debug("Learn approximation for $call:\n$approximation")
        approximationManager.update(call, approximation)
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

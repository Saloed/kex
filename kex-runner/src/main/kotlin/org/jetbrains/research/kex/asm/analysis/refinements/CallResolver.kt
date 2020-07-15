package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ir.Method
import java.time.Period

class CallResolver(val methodAnalyzer: MethodAnalyzer, val approximationManager: MethodApproximationManager) {
    fun resolveCalls(state: PredicateState): PredicateState {
        val calls = unresolvedCalls(state)
        if (calls.isEmpty()) return state
        if (calls.size > 1) {
            TODO("Too many calls to resolve")
        }
        val call = calls.last()
        val callPrecondition = resolveSingleCall(state, call)
        val callPostCondition = state.filter { it != call }
        val approximation = MethodUnderApproximation(callPrecondition, callPostCondition)
        approximationManager.update(call, approximation)
        return state
    }

    private fun unresolvedCalls(state: PredicateState) = PredicateCollector.collectIsInstance<CallPredicate>(state)

    private fun resolveCallsLoop(stateGenerator: () -> PredicateState): PredicateState {
        var state = stateGenerator()
        while (true) {
            state = resolveCalls(state)
            if (unresolvedCalls(state).isEmpty()) break
            state = stateGenerator()
        }
        return state
    }

    private fun preprocessState(state: PredicateState, suffixGen: TermSuffixGenerator, argMapper: TermRemapper): PredicateState {
        // todo: inheritance
        val withApproximations = approximationManager.extendWithUnderApproximations(state)
        val methodState = CalledMethodInliner(methodAnalyzer.psa, suffixGen).apply(withApproximations)
        return argMapper.apply(methodState)
    }

    private fun postProcessState(state: PredicateState, argMapper: TermRemapper): PredicateState {
        return argMapper.apply(state)
    }

    private fun collectArguments(state: PredicateState, call: CallPredicate): Triple<List<Term>, TermRemapper, TermRemapper> {
        val callArguments = VariableCollector().apply { transform(call.call) }.variables.toList()
        val (solutionThis, solutionOtherArgs) = collectArguments(state)
        val arguments = solutionOtherArgs.values + callArguments + listOfNotNull(solutionThis)
        val argumentsMapping = arguments.map { arg -> arg to term { value(arg.type, "refine_arg_${arg.name}") } }.toMap()
        val backwardMapping = argumentsMapping.map { it.value to it.key }.toMap()
        val argumentTerms = backwardMapping.keys.toList()
        return Triple(argumentTerms, TermRemapper(argumentsMapping), TermRemapper(backwardMapping))
    }

    private fun resolveSingleCall(state: PredicateState, call: CallPredicate): PredicateState {
        val (arguments, forwardMapping, backwardMapping) = collectArguments(state, call)
        val negatedState = state.negateWRTStatePredicates().optimize()
        val suffixGen = TermSuffixGenerator()
        val resolver = CallResolver(methodAnalyzer, approximationManager)
        val finalResult = resolver.resolveCallsLoop {
            val positiveState = preprocessState(state, suffixGen, forwardMapping)
            val negativeState = preprocessState(negatedState, suffixGen, forwardMapping)
            log.debug("Resolve call:\nPositive:\n$positiveState\nNegative:\n$negativeState")
            val solverResult = queryFixpointSolver(positiveState, negativeState, arguments)
            val result = postProcessState(solverResult, backwardMapping)
            result
        }
        return finalResult
    }

    private fun queryFixpointSolver(positive: PredicateState, negative: PredicateState, arguments: List<Term>): PredicateState {
        val solverResult = Z3FixpointSolver(methodAnalyzer.cm.type).refineWithFixpointSolver(positive, negative, arguments)
        val result = when (solverResult) {
            is FixpointResult.Sat -> solverResult.result.first()
            is FixpointResult.Unknown -> {
                log.error("Unknown: ${solverResult.reason}")
                falseState()
            }
            is FixpointResult.Unsat -> {
                log.error("Unsat: ${solverResult.core.contentToString()}")
                falseState()
            }
        }
        return result
    }

    private class TermSuffixGenerator {
        private var inlineIndex = 0
        private val suffixCache = hashMapOf<CallPredicate, String>()
        fun getSuffix(call: CallPredicate) = suffixCache.getOrPut(call) { "inlined${inlineIndex++}" }
    }

    private open class CalledMethodInliner(psa: PredicateStateAnalysis, val suffixGen: TermSuffixGenerator) : MethodInliner(psa) {
        override fun renameTermsAfterInlining(call: CallPredicate, state: PredicateState, mappings: Map<Term, Term>): PredicateState {
            return TermRenamer(suffixGen.getSuffix(call), mappings).apply(state)
        }

        override fun methodState(method: Method): PredicateState? {
            val methodState = super.methodState(method) ?: return null
            val constructorsInlined = ConstructorDeepInliner(psa).apply(methodState)
            val noIntrinsics = IntrinsicAdapter.apply(constructorsInlined)
            return noIntrinsics
        }
    }
}
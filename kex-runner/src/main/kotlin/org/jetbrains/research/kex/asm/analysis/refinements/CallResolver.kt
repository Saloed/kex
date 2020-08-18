package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.debug
import com.abdullin.kthelper.logging.log
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.asm.analysis.refinements.solver.FixpointSolver
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.TermDependency
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.memory.MemoryAccess
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.FieldTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.*

class CallResolver(val methodAnalyzer: MethodAnalyzer, val approximationManager: MethodApproximationManager) {

    interface Argument<T : Argument<T>> {
        fun transform(transformer: (PredicateState) -> PredicateState): T
        fun updateIgnoredCalls(transformer: (Set<CallPredicate>) -> Set<CallPredicate>): T
    }

    inline fun <reified T : Argument<T>> callResolutionLoopMany(argument: T, crossinline processor: (T) -> List<RecoveredModel>): List<PredicateState> {
        while (true) {
            log.debug("Enter call resolution loop for ${methodAnalyzer.method}")
            val callArgument = argument.transform { approximationManager.extendWithUnderApproximations(it) }
            val callArgumentWithIgnoredCalls = ignoreCalls(callArgument)
            val processed = processor(callArgumentWithIgnoredCalls)
            if (processed.all { it.isFinal }) return processed.map { it.finalStateOrException() }
            processed.forEach { resolveCalls(it) }
        }
    }

    fun <T : Argument<T>> ignoreCalls(argument: T): T {
        val callCollector = PredicateCollector { it is CallPredicate }
        argument.transform { callCollector.transform(it); it }
        val allCalls = callCollector.predicates.filterIsInstance<CallPredicate>().toSet()
        return argument.updateIgnoredCalls { ignored ->
            val callsToCheck = allCalls - ignored
            val callsToIgnore = callsToCheck.filter { callMayBeIgnored(it) }
            ignored + callsToIgnore
        }
    }

    private fun callMayBeIgnored(call: CallPredicate): Boolean {
        val approximation = approximationManager.underApproximations[call] ?: return false
        return approximation.approximations.isNotEmpty()
    }

    inline fun <reified T : Argument<T>> callResolutionLoop(argument: T, crossinline processor: (T) -> RecoveredModel): PredicateState =
            callResolutionLoopMany(argument) { listOf(processor(it)) }.first()

    fun resolveCalls(model: RecoveredModel) {
        if (model.isFinal) return
        val calls = model.dependencies.groupBy { it.call }
        if (calls.isEmpty()) return
        if (calls.size > 1) return tryResolveMultipleCalls(model)
        val (call, dependencies) = calls.entries.last()
        resolveSingleCall(model.state, call, dependencies)
    }

    private fun tryResolveMultipleCalls(model: RecoveredModel) {
        val maxId = model.dependencies.map { it.callIdx }.maxOrNull() ?: error("impossible")
        val depsToResolve = model.dependencies.filter { it.callIdx == maxId }
        val callToResolve = depsToResolve.first().call
        resolveSingleCall(model.state, callToResolve, depsToResolve)
    }

    private fun resolveSingleCall(state: PredicateState, call: CallPredicate, dependencies: List<TermDependency>) {
        val callPreconditions = resolveCalls(state, listOf(call), dependencies)
        approximationManager.update(call, MethodUnderApproximation(callPreconditions, state))
    }

    private fun resolveCalls(state: PredicateState, calls: List<CallPredicate>, dependencies: List<TermDependency>): PredicateState {
        val (arguments, forwardMapping, backwardMapping) = collectArguments(state, calls, dependencies)
        val suffixGen = TermSuffixGenerator()
        val positiveState = preprocessState(state, suffixGen, dependencies, forwardMapping)
        val negativeState = positiveState.negateWRTStatePredicates().optimize()
        MemoryUtils.verifyVersions(positiveState)
        MemoryUtils.verifyVersions(negativeState)

//        MemoryUtils.view(positiveState)

        val argument = SolverArgument(positiveState, negativeState, arguments, emptySet())
        val resolver = CallResolver(methodAnalyzer, approximationManager)
        val result = resolver.callResolutionLoop(argument) { solverArg ->
            log.debug(solverArg)
            val result = FixpointSolver(methodAnalyzer.cm).querySingle(
                    {
                        it.dumpSolverArguments(solverArg, debug = true)
                        MemoryUtils.verifyVersions(solverArg.positive)
                        MemoryUtils.verifyVersions(solverArg.negative)
                        refineWithFixpointSolver(solverArg.positive, solverArg.negative, solverArg.arguments)
                    },
                    { ex ->
                        dumpSolverArguments(solverArg)
                        throw IllegalStateException("$ex")
                    }
            )
            log.debug(result)
            result
        }
        return postprocessState(result, backwardMapping)
    }

    private fun preprocessState(state: PredicateState, suffixGen: TermSuffixGenerator, dependencies: List<TermDependency>, forwardMapping: TermRemapper): PredicateState {
        val stateWithDependencyInlined = inlineCallDependencies(state, methodAnalyzer.psa, suffixGen, dependencies)
        return transform(stateWithDependencyInlined) {
            +forwardMapping
        }.optimize()
    }

    private fun postprocessState(state: PredicateState, backwardMapping: TermRemapper): PredicateState = transform(state) {
        +backwardMapping
    }

    private fun inlineCallDependencies(state: PredicateState, psa: PredicateStateAnalysis, suffixGen: TermSuffixGenerator, dependencies: List<TermDependency>): PredicateState {
        val callsToInline = dependencies.map { it.call.call as CallTerm }.distinct()
        check(callsToInline.size == 1) { "Too many calls to inline" }
        val call = callsToInline.first()
        val inlineStatus = MethodManager.InlineManager.isInlinable(call.method)
        if (inlineStatus == MethodManager.InlineManager.InlineStatus.NO_INLINE) error("Method is not inlineable")
        if (inlineStatus == MethodManager.InlineManager.InlineStatus.MAY_INLINE) TODO("Inheritance")

        val mappings = hashMapOf<Term, Term>()
        if (!call.isStatic) {
            val `this` = term { `this`(call.owner.type) }
            mappings[`this`] = call.owner
        }
        for ((index, argType) in call.method.argTypes.withIndex()) {
            val argTerm = term { arg(argType.kexType, index) }
            val calledArg = call.arguments[index]
            mappings[argTerm] = calledArg
        }
        val retval = term { `return`(call.method) }
        val retvalPlaceholder = term { value(retval.type, "retval_${call.hashCode()}") }
        mappings[retval] = retvalPlaceholder

        check(call.method.isNotEmpty()) { "Try to inline empty method" }

        val methodState = psa.builder(call.method).methodState ?: error("No state for method ${call.method}")
        val endState = transform(methodState) {
            +ConstructorDeepInliner(psa)
//                +SimpleMethodInliner(psa)
            +IntrinsicAdapter
        }
        val preparedMethodState = renameTermsAfterInlining(call, endState, mappings, suffixGen)
        val retvalBindings = basic {
            dependencies.filterIsInstance<TermDependency.CallResultDependency>().forEach { dependency ->
                predicate(PredicateType.State()) { dependency.term equality retvalPlaceholder }
            }
        }
        val methodStateForInlining = ChainState(preparedMethodState, retvalBindings)
        MemoryUtils.newAsSeparateInitialVersions(state)
        val (updatedState, versionedMethodState) = MemoryUtils.initializeMemoryVersionsAndPrepareForReplacement(state, methodStateForInlining, call.memoryVersion)

        return ChainState(versionedMethodState, updatedState)
    }

    private fun renameTermsAfterInlining(call: CallTerm, state: PredicateState, mappings: Map<Term, Term>, suffixGen: TermSuffixGenerator): PredicateState {
        return MethodInliner.TermRenamer(suffixGen.getSuffix(call), mappings).apply(state)
    }

    private fun collectArguments(state: PredicateState, calls: List<CallPredicate>, dependencies: List<TermDependency>): Triple<List<Term>, TermRemapper, TermRemapper> {
        val callArguments = calls.flatMap { call -> VariableCollector().apply { transform(call.call) }.variables }
        val callResultDependentTerms = dependencies.filterIsInstance<TermDependency.CallResultDependency>().map { it.term }.toSet()
        val memoryDependency = dependencies.filterIsInstance<TermDependency.MemoryDependency>().map { it.memoryAccess }.toSet()
        val stateArguments = collectVariables(state)
                .filterNot { it is FieldTerm }
                .filterNot { it in callResultDependentTerms }
                .filterNot { it is MemoryAccess<*> && it in memoryDependency }
        val argumentsMapping = (callArguments + stateArguments).distinct().mapIndexed { i, term -> term to term { arg(term.type, i) } }.toMap()
        val backwardMapping = argumentsMapping.entries.associateBy({ it.value }, { it.key })
        val argumentTerms = backwardMapping.keys.toList()
        return Triple(argumentTerms, TermRemapper(argumentsMapping), TermRemapper(backwardMapping))
    }

    @Serializable
    data class SolverArgument(val positive: PredicateState, val negative: PredicateState, val arguments: List<Term>, val ignoredCalls: Set<CallPredicate>) : Argument<SolverArgument> {
        override fun transform(transformer: (PredicateState) -> PredicateState): SolverArgument = SolverArgument(transformer(positive), transformer(negative), arguments, ignoredCalls)
        override fun updateIgnoredCalls(transformer: (Set<CallPredicate>) -> Set<CallPredicate>): SolverArgument = SolverArgument(positive, negative, arguments, transformer(ignoredCalls))
        override fun toString(): String = "Resolve call solver argument:\nPositive:\n$positive\nNegative:\n$negative"
    }

    private class TermSuffixGenerator {
        private var inlineIndex = 0
        private val suffixCache = hashMapOf<CallTerm, String>()
        fun getSuffix(call: CallTerm) = suffixCache.getOrPut(call) { "inlined${inlineIndex++}" }
    }

}
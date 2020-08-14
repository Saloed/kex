package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.debug
import com.abdullin.kthelper.logging.log
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.asm.analysis.refinements.solver.FixpointSolver
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.fixpoint.DependencyType
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.TermDependency
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.FieldTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ir.Method

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
        val calls = model.callDependencies.groupBy { it.call }
        if (calls.isEmpty()) return
        if (calls.size > 1) return tryResolveMultipleCalls(model)
        val (call, dependencies) = calls.entries.last()
        resolveSingleCall(model.state, call, dependencies)
    }

    private fun tryResolveMultipleCalls(model: RecoveredModel) {
        val maxId = model.callDependencies.map { it.callIdx }.maxOrNull() ?: error("impossible")
        val depsToResolve = model.callDependencies.filter { it.callIdx == maxId }
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
        val argument = SolverArgument(positiveState, negativeState, arguments, emptySet())
        val resolver = CallResolver(methodAnalyzer, approximationManager)
        val result = resolver.callResolutionLoop(argument) { solverArg ->
            log.debug(solverArg)
            val result = FixpointSolver(methodAnalyzer.cm).querySingle(
                    { refineWithFixpointSolver(solverArg.positive, solverArg.negative, solverArg.arguments) },
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

    private fun preprocessState(state: PredicateState, suffixGen: TermSuffixGenerator, dependencies: List<TermDependency>, forwardMapping: TermRemapper): PredicateState =
            transform(state) {
                +CallDependencyResolver(methodAnalyzer.psa, suffixGen, dependencies)
                +forwardMapping
            }

    private fun postprocessState(state: PredicateState, backwardMapping: TermRemapper): PredicateState = transform(state) {
        +backwardMapping
    }

    private class CallDependencyResolver(val psa: PredicateStateAnalysis, val suffixGen: TermSuffixGenerator, dependencies: List<TermDependency>) : RecollectingTransformer<MethodInliner> {
        private val termDependencies = dependencies.map { it.term to it }.toMap()
        private val im = MethodManager.InlineManager
        override val builders = dequeOf(StateBuilder())

        override fun transformTerm(term: Term): Term {
            val res = super.transformTerm(term)
            val dependency = termDependencies[res] ?: return res
            resolveDependency(dependency)
            return term
        }

        private fun resolveDependency(dependency: TermDependency) {
            val call = dependency.call.call as CallTerm
            val calledMethod = call.method
            val inlineStatus = im.isInlinable(calledMethod)
            if (inlineStatus == MethodManager.InlineManager.InlineStatus.NO_INLINE) return
            if (inlineStatus == MethodManager.InlineManager.InlineStatus.MAY_INLINE) TODO("Inheritance")
            val mappings = callArgumentMapping(call, dependency)
            currentBuilder += methodState(call, calledMethod, mappings) ?: return
        }

        fun callArgumentMapping(call: CallTerm, dependency: TermDependency): Map<Term, Term> {
            val calledMethod = call.method
            val mappings = hashMapOf<Term, Term>()
            if (!call.isStatic) {
                val `this` = term { `this`(call.owner.type) }
                mappings[`this`] = call.owner
            }
            for ((index, argType) in calledMethod.argTypes.withIndex()) {
                val argTerm = term { arg(argType.kexType, index) }
                val calledArg = call.arguments[index]
                mappings[argTerm] = calledArg
            }
            if (dependency.type == DependencyType.RETURN_VALUE) {
                val retval = term { `return`(calledMethod) }
                mappings[retval] = dependency.term
            }
            return mappings
        }

        fun methodState(call: CallTerm, method: Method, mappings: Map<Term, Term>): PredicateState? {
            if (method.isEmpty()) return null
            val methodState = psa.builder(method).methodState ?: return null
            val endState = transform(methodState) {
                +ConstructorDeepInliner(psa)
                +IntrinsicAdapter
            }
            return renameTermsAfterInlining(call, endState, mappings)
        }

        fun renameTermsAfterInlining(call: CallTerm, state: PredicateState, mappings: Map<Term, Term>): PredicateState {
            return MethodInliner.TermRenamer(suffixGen.getSuffix(call), mappings).apply(state)
        }

    }

    private fun collectArguments(state: PredicateState, calls: List<CallPredicate>, dependencies: List<TermDependency>): Triple<List<Term>, TermRemapper, TermRemapper> {
        val dependentTerms = dependencies.map { it.term }.toSet()
        val callArguments = calls.flatMap { call -> VariableCollector().apply { transform(call.call) }.variables }
        val stateArguments = collectVariables(state).filter { it !is FieldTerm }.filter { it !in dependentTerms }
        val argumentsMapping = (callArguments + stateArguments).map { arg -> arg to term { value(arg.type, "refine_arg_${arg.name}") } }.toMap()
        val backwardMapping = argumentsMapping.map { it.value to it.key }.toMap()
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
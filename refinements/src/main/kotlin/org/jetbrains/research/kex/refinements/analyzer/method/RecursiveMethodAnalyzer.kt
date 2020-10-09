package org.jetbrains.research.kex.refinements.analyzer.method

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.state.PredicateStateBuilder
import org.jetbrains.research.kex.ktype.KexArray
import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexPointer
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.refinements.*
import org.jetbrains.research.kex.refinements.analyzer.utils.MethodCallCollector
import org.jetbrains.research.kex.refinements.analyzer.utils.MethodExecutionPathsAnalyzer
import org.jetbrains.research.kex.refinements.analyzer.exceptions.ExceptionSource
import org.jetbrains.research.kex.refinements.analyzer.exceptions.PredicateStateBuilderWithThrows
import org.jetbrains.research.kex.refinements.analyzer.sources.RecursiveRefinementSourcesAnalyzer
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.FieldLoadTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.StringName
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.ir.value.instruction.CallOpcode
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst
import ru.spbstu.ktuples.zip

class RecursiveMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    override fun analyze(): Refinements {
        log.info("Analyze recursive method: $method")
        val recursiveTraces = methodRecursiveCallTraces()
        if (recursiveTraces.any { it.size > 1 }) {
            TODO("Co-recursion is not supported yet")
        }
        val directRecursiveCalls = recursiveTraces.map { it.last() }

        val methodPaths = MethodExecutionPathsAnalyzer(cm, psa, method)
        val state = buildMethodState(methodPaths, skipInlining = { it == method })
        val (nestedNormal, nestedRefinementSources) = inlineRefinements(ignoredCalls = directRecursiveCalls)

        val rootCall = createRootCall()
        val recursionPaths = findPathsLeadsToRecursion(directRecursiveCalls, methodPaths.builder)

        val allSources = methodPaths.exceptionalExecutionPaths.merge(nestedRefinementSources)
                .fmap { it.filterRecursiveCalls() }
                .fmap { it.optimize() }
        val allNormal = ChainState(methodPaths.normalExecutionPaths, nestedNormal)
                .filterRecursiveCalls()
                .optimize()
        val forMemspacing = MemspacingArguments(state, recursionPaths, allNormal, allSources)
        val (afterMemspace, recursiveCalls) = memspaceWithRecursionInfo(forMemspacing)
        if (recursiveCalls.isEmpty()) {
            throw IllegalArgumentException("No recursive calls to analyze")
        }

        log.debug("State:\n${afterMemspace.state}\nRecursion:\n${afterMemspace.recursion}\nNormal:\n${afterMemspace.normal}\nSources:\n${afterMemspace.sources}")
        return RecursiveRefinementSourcesAnalyzer(this)
                .analyze(afterMemspace.state, afterMemspace.normal, afterMemspace.sources, rootCall, recursiveCalls, afterMemspace.recursion)
    }

    private data class MemspacingArguments(val state: PredicateState, val recursion: PredicateState, val normal: PredicateState, val sources: RefinementSources)

    private fun PredicateState.filterRecursiveCalls(): PredicateState =
            filterNot { it is CallPredicate && (it.call as CallTerm).method == method }


    private fun createRootCall(): CallPredicate = state {
        val arguments = method.argTypes.withIndex().map { (index, argType) ->
            term { arg(argType.kexType, index) }
        }
        val returnTerm = term { `return`(method) }
        val owner = when {
            method.isStatic -> term { `class`(method.`class`) }
            else -> term { value(method.`class`.kexType, "owner") }
        }
        val instruction = CallInst(CallOpcode.Special(), StringName("recursion_root_call"), method, method.`class`, emptyArray())
        val methodCall = term { tf.getCall(method, instruction, owner, arguments) }
        returnTerm.call(methodCall)
    } as CallPredicate

    private fun memspaceWithRecursionInfo(forMemspacing: MemspacingArguments): Pair<MemspacingArguments, Map<CallPredicate, Map<Field, FieldLoadTerm>>> {
        val state = forMemspacing.state
        val recursiveCalls = stateRecursiveCalls(state)
        val callProperties = recursiveCalls.map { callMemoryProperties(it) }
        var expandedState = state
        for ((callPredicate, properties) in recursiveCalls.zip(callProperties)) {
            val dummyEqualities = properties.values.map { state { it equality it } }
            expandedState = expandedState.insertBefore(callPredicate, BasicState(dummyEqualities))
        }
        val allStates = listOf(expandedState) + forMemspacing.sources.value.map { it.condition } + listOf(forMemspacing.normal, forMemspacing.recursion)
        val memorySpacer = MemorySpacer(ChoiceState(allStates))
        val result = MemspacingArguments(
                memorySpacer.apply(forMemspacing.state),
                memorySpacer.apply(forMemspacing.recursion),
                memorySpacer.apply(forMemspacing.normal),
                forMemspacing.sources.fmap { memorySpacer.apply(it) }
        )
        val callInfo = mutableMapOf<CallPredicate, Map<Field, FieldLoadTerm>>()
        for ((callPredicate, properties) in recursiveCalls.zip(callProperties)) {
            val propertiesWithMemspace = properties.mapValues { (_, term) -> memorySpacer.transform(term) as FieldLoadTerm }
            val callWithMemspace = memorySpacer.transform(callPredicate) as CallPredicate
            callInfo[callWithMemspace] = propertiesWithMemspace
        }
        return result to callInfo
    }

    private fun callMemoryProperties(callPredicate: CallPredicate): Map<Field, FieldLoadTerm> {
        val call = callPredicate.call as CallTerm
        val arguments = listOf(call.owner) + call.arguments
        return arguments.filter { it.type is KexPointer }
                .flatMap { expandProperties(it) }
                .toMap()
    }

    private fun stateRecursiveCalls(state: PredicateState): List<CallPredicate> {
        val recursiveCalls = arrayListOf<CallPredicate>()
        state.map {
            if (it is CallPredicate && (it.call as CallTerm).method == method) {
                recursiveCalls.add(it)
            }
            it
        }
        return recursiveCalls
    }

    private fun PredicateState.insertBefore(predicate: Predicate, state: PredicateState): PredicateState = when (this) {
        is BasicState -> when {
            predicate !in predicates -> this
            else -> {
                val before = arrayListOf<Predicate>()
                val after = arrayListOf<Predicate>()
                var isBefore = true
                for (it in predicates) {
                    if (it == predicate) isBefore = false
                    val predicateSet = if (isBefore) before else after
                    predicateSet.add(it)
                }
                (StateBuilder() + BasicState(before) + state + BasicState(after)).apply()
            }
        }
        else -> fmap { it.insertBefore(predicate, state) }
    }


    private fun expandProperties(obj: Term) = when (val type = obj.type) {
        is KexClass -> {
            val fields = type.getKfgClass(cm.type).fields.toList()
            val fieldTerms = fields.map { term { obj.field(it.type.kexType, it) } }
            val loads = fieldTerms.map { term { it.load() } as FieldLoadTerm }
            fields.zip(loads)
        }
        is KexArray -> TODO("Array argument in recursive function")
        else -> emptyList()
    }

    private fun MethodFunctionalInliner.TransformationState.getMethodStateAndRefinement(): Pair<Refinements, PredicateState> {
        val refinement = findRefinement(calledMethod).expanded()
        val methodState = getStateForInlining()
        if (refinement.isUnknown() && methodState == null) skip()
        val state = methodState ?: BasicState()
        return refinement to state
    }

    private fun methodRecursiveCallTraces(): List<List<CallInst>> {
        fun go(method: Method, methodTrace: List<Method>, trace: List<CallInst>): List<List<CallInst>> =
                when (method) {
                    this.method -> listOf(trace)
                    in methodTrace -> emptyList()
                    else -> MethodCallCollector.calls(cm, method)
                            .flatMap { go(it.method, methodTrace + listOf(method), trace + listOf(it)) }
                            .filter { it.isNotEmpty() }
                }

        return MethodCallCollector.calls(cm, method)
                .flatMap { go(it.method, listOf(method), listOf(it)) }
                .filter { it.isNotEmpty() }
    }


    private fun findPathsLeadsToRecursion(calls: List<CallInst>, psb: PredicateStateBuilder) = calls
            .mapNotNull { psb.getInstructionState(it) }
            .map {
                MethodFunctionalInliner(psa) {
                    if (calledMethod == method) skip()
                    var state = getStateForInlining() ?: skip()
                    state = fixPathPredicatesOnTopLevelBeforeInlining(state)
                    inline(state)
                }.apply(it)
            }
            .map { it.path }
            .let { ChoiceState(it) }
            .optimize()

    fun inlineRefinements(ignoredCalls: List<CallInst> = emptyList()): Pair<PredicateState, RefinementSources> {
        val calls = MethodCallCollector.calls(cm, method).filterNot { it in ignoredCalls }
        val refinements = calls.map { findRefinement(it.method) }
        val exceptionalPaths = buildRefinementSources(calls, refinements, ignoredCalls)
        val normalPath = buildNormalPaths(calls, refinements)
        return normalPath to exceptionalPaths
    }

    private fun buildMethodState(builder: MethodExecutionPathsAnalyzer, skipInlining: (Method) -> Boolean = { false }): PredicateState {
        val (preparedState, otherExecutionPaths) = prepareMethodState(builder, skipInlining)
        val transformedTopChoices = prepareMethodOtherExecutionPaths(otherExecutionPaths, skipInlining)
        val interestingTopChoices = transformedTopChoices
                .map { it.optimize() }
                .filterNot { it.evaluatesToTrue || it.evaluatesToFalse }
        val state = when {
            interestingTopChoices.isEmpty() -> preparedState
            else -> ChoiceState(listOf(preparedState) + interestingTopChoices)
        }
        return transform(state) {
            applyAdapters(this@RecursiveMethodAnalyzer)
        }
    }


    private fun prepareMethodOtherExecutionPaths(otherExecutionPaths: List<PredicateState>, skipInlining: (Method) -> Boolean): List<PredicateState> =
            otherExecutionPaths.map {
                MethodFunctionalInliner(psa) {
                    if (skipInlining(calledMethod)) skip()
                    val (refinement, methodState) = getMethodStateAndRefinement()
                    val fixedState = fixPathPredicatesOnTopLevelBeforeInlining(methodState)
                    val state = ChainState(refinement.allStates().negateWRTStatePredicates(), fixedState)
                    inline(state)
                }.apply(it)
            }

    private fun prepareMethodState(builder: MethodExecutionPathsAnalyzer, skipInlining: (Method) -> Boolean): Pair<PredicateState, List<PredicateState>> {
        val otherExecutionPaths = mutableListOf<PredicateState>()
        val inlinedState = transform(builder.methodRawFullState()) {
            +MethodFunctionalInliner(psa) {
                if (skipInlining(calledMethod)) skip()
                val instruction = predicate.instruction
                val instructionState = psa.builder(method).getInstructionState(instruction)
                        ?: throw IllegalStateException("No state for call")
                val (refinement, methodState) = getMethodStateAndRefinement()
                val fixedState = fixPathPredicatesOnTopLevelBeforeInlining(methodState)
                val state = ChainState(refinement.allStates().negateWRTStatePredicates(), fixedState)
                inline(state)
                val inlinedNegative = prepareForInline(refinement.allStates())
                val withoutCurrentCall = instructionState.filterNot { it == predicate }
                val negativeExecution = ChainState(withoutCurrentCall, inlinedNegative)
                otherExecutionPaths.add(negativeExecution)
            }
        }
        return inlinedState to otherExecutionPaths
    }

    private fun buildRefinementSources(calls: List<CallInst>, refinements: List<Refinements>, ignoredCalls: List<CallInst>): RefinementSources {
        val builder = psa.builder(method)
        val result = arrayListOf<RefinementSource>()
        val refinementMap = calls.zip(refinements).toMap()
        for ((call, refinement) in zip(calls, refinements)) {
            val otherCalls = refinementMap
                    .filterKeys { it != call }
                    .mapValues { it.value.allStates().negateWRTStatePredicates() }
            val (state, callInstructions) = nestedMethodCallStates(builder, call)
            for (reft in refinement.expanded().value) {
                val mapping = otherCalls + (call to reft.state.toPredicateState())
                val refSource = buildRefinementSource(reft.criteria, state, mapping, callInstructions, ignoredCalls)
                result.add(refSource)
            }
        }
        return RefinementSources.create(result).simplify()
    }

    private fun buildRefinementSource(
            criteria: RefinementCriteria,
            state: PredicateState,
            mapping: Map<CallInst, PredicateState>,
            callInstructions: Map<CallPredicate, CallInst>,
            ignoredCalls: List<CallInst>
    ): RefinementSource {
        val inliner = MethodFunctionalInliner(psa) {
            val instruction = callInstructions[predicate]
                    ?: throw IllegalStateException("No instruction for predicate")
            if (instruction in ignoredCalls) skip()
            val predicateState = mapping[instruction]
                    ?: throw IllegalArgumentException("No method $predicate for inline")
            inline(predicateState)
        }
        val resultPath = inliner.apply(state)
        return RefinementSource.create(criteria, resultPath)
    }

    private fun buildNormalPaths(calls: List<CallInst>, refinements: List<Refinements>): PredicateState {
        val builder = PredicateStateBuilderWithThrows.forMethod(method)
        val predicates = calls.map {
            builder.findPredicateForInstruction(it)
        }
        val allInlined = zip(predicates, refinements).map { (predicate, refinement) ->
            val inliner = MethodFunctionalInliner(psa) { inline(refinement.allStates()) }
            inliner.apply(predicate.wrap())
        }
        return ChoiceState(allInlined).negateWRTStatePredicates()
    }

    private fun nestedMethodCallStates(psb: PredicateStateBuilder, call: CallInst): Pair<PredicateState, Map<CallPredicate, CallInst>> {
        val state = (psb.getInstructionState(call) ?: BasicState())
                .filter { it is CallPredicate || it.type == PredicateType.Path() }
        val callPredicates = PredicateCollector.collectIsInstance<CallPredicate>(state)
        val callInstructions = callPredicates.map {
            it.instruction as? CallInst
                    ?: throw IllegalStateException("Cant find instruction for call")
        }
        val callMap = callPredicates.zip(callInstructions).toMap()
        return state to callMap
    }

    private val MethodExecutionPathsAnalyzer.exceptionalExecutionPaths
        get() = throws
                .map { getRefinementCriteria(it) to builder.getInstructionState(it) }
                .filter { it.second != null }
                .map { it.first to it.second!!.path }
                .map { RefinementSource.create(it.first, it.second) }
                .let { RefinementSources.create(it) }
                .simplify()

    private val MethodExecutionPathsAnalyzer.normalExecutionPaths
        get() = returns
                .mapNotNull { builder.getInstructionState(it) }
                .map { it.path }
                .let { ChoiceState(it) }

    private fun MethodExecutionPathsAnalyzer.getRefinementCriteria(inst: Instruction) = when (inst) {
        is ThrowInst -> ExceptionSource.MethodException(inst).refinementCriteria
        else -> TODO("Unsupported refinement criteria: $inst")
    }
}

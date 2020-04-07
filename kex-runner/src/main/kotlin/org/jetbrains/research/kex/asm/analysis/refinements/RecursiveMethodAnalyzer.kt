package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.state.PredicateStateBuilder
import org.jetbrains.research.kex.ktype.KexArray
import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexPointer
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.FieldLoadTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst

class RecursiveMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

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


    override fun analyze(): Refinements {
        log.info("Analyze recursive method: $method")
        val recursiveTraces = methodRecursiveCallTraces()
        if (recursiveTraces.any { it.size > 1 }) {
            TODO("Co-recursion is not supported yet")
        }
        val directRecursiveCalls = recursiveTraces.map { it.last() }

        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, method)
        val (state, recursiveCalls) = buildMethodState(methodPaths)
        if (recursiveCalls.isEmpty()) {
            throw IllegalArgumentException("No recursive calls to analyze")
        }

        val (nestedNormal, nestedRefinementSources) = inlineRefinements(ignoredCalls = directRecursiveCalls)

        val rootCall = createRootCall()
        val recursionPaths = findPathsLeadsToRecursion(directRecursiveCalls, methodPaths.builder)

        val allSources = methodPaths.refinementSources.merge(nestedRefinementSources)
                .fmap { it.filterRecursiveCalls() }
                .fmap { it.optimize() }
        val allNormal = ChainState(methodPaths.normalExecutionPaths, nestedNormal)
                .filterRecursiveCalls()
                .optimize()

        log.info("State:\n$state\nRecursion:\n$recursionPaths\nNormal:\n$allNormal\nSources:\n$allSources")

        val refinements = allSources.value.map {
            computeRefinement(state, rootCall, recursiveCalls, recursionPaths, allNormal, it)
        }
        return Refinements(refinements, method)
    }

    private fun PredicateState.filterRecursiveCalls(): PredicateState =
            filterNot { it is CallPredicate && (it.callTerm as CallTerm).method == method }

    private fun computeRefinement(
            state: PredicateState,
            rootCall: CallPredicate,
            recursiveCalls: Map<CallPredicate, Map<Field, FieldLoadTerm>>,
            recursionPaths: PredicateState,
            normalPaths: PredicateState,
            refinementSource: RefinementSource
    ): Refinement {
        val solver = Z3FixpointSolver(cm.type)
        val refinement: PredicateState = try {
            val result = solver.analyzeRecursion(state, recursiveCalls, rootCall, recursionPaths, refinementSource.condition, normalPaths)
            when (result) {
                is FixpointResult.Sat -> result.result.first()
                else -> {
                    if (result is FixpointResult.Unknown) log.error("Unknown: ${result.reason}")
                    falseState()
                }
            }
        } catch (ex: QueryCheckStatus.FixpointQueryException) {
            log.error("Bad fixpoint query: ${ex.status}")
            falseState()
        }
        return Refinement.create(refinementSource.criteria, refinement)
    }

    private fun createRootCall(): CallPredicate = state {
        val arguments = method.argTypes.withIndex().map { (index, argType) ->
            term { arg(argType.kexType, index) }
        }
        val returnTerm = term { `return`(method) }
        val owner = when {
            method.isStatic -> term { `class`(method.`class`) }
            else -> term { value(method.`class`.kexType, "owner") }
        }
        val methodCall = term { tf.getCall(method, owner, arguments) }
        returnTerm.call(methodCall)
    } as CallPredicate


    private fun buildMethodState(builder: MethodRefinementSourceAnalyzer): Pair<PredicateState, Map<CallPredicate, Map<Field, FieldLoadTerm>>> {
        val (preparedState, otherExecutionPaths) = prepareMethodState(builder)
        val transformedTopChoices = prepareMethodOtherExecutionPaths(otherExecutionPaths)
        val interestingTopChoices = transformedTopChoices
                .map { it.optimize() }
                .filterNot { it.evaluatesToTrue || it.evaluatesToFalse }
        var state = when {
            interestingTopChoices.isEmpty() -> preparedState
            else -> ChoiceState(listOf(preparedState) + interestingTopChoices)
        }
        state = transform(state) {
            applyAdapters()
        }
        return memspaceWithRecursionInfo(state)
    }


    private fun memspaceWithRecursionInfo(state: PredicateState): Pair<PredicateState, Map<CallPredicate, Map<Field, FieldLoadTerm>>> {
        val recursiveCalls = stateRecursiveCalls(state)
        val callProperties = recursiveCalls.map { callMemoryProperties(it) }
        var expandedState = state
        for ((callPredicate, properties) in recursiveCalls.zip(callProperties)) {
            val dummyEqualities = properties.values.map { state { it equality it } }
            expandedState = expandedState.insertBefore(callPredicate, BasicState(dummyEqualities))
        }
        val memorySpacer = MemorySpacer(expandedState)
        val resultState = memorySpacer.apply(state)

        val callInfo = mutableMapOf<CallPredicate, Map<Field, FieldLoadTerm>>()
        for ((callPredicate, properties) in recursiveCalls.zip(callProperties)) {
            val propertiesWithMemspace = properties.mapValues { (_, term) -> memorySpacer.transform(term) as FieldLoadTerm }
            val callWithMemspace = memorySpacer.transform(callPredicate) as CallPredicate
            callInfo[callWithMemspace] = propertiesWithMemspace
        }
        return resultState to callInfo
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
            val fieldTerms = fields.map { term { obj.field(it.type.kexType, it.name) } }
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

    private fun prepareMethodOtherExecutionPaths(otherExecutionPaths: List<PredicateState>): List<PredicateState> =
            otherExecutionPaths.map {
                MethodFunctionalInliner(psa) {
                    if (calledMethod == method) skip()
                    val (refinement, methodState) = getMethodStateAndRefinement()
                    val fixedState = fixPathPredicatesOnTopLevelBeforeInlining(methodState)
                    val state = ChainState(refinement.allStates().not(), fixedState)
                    inline(state)
                }.apply(it)
            }

    private fun prepareMethodState(builder: MethodRefinementSourceAnalyzer): Pair<PredicateState, List<PredicateState>> {
        val otherExecutionPaths = mutableListOf<PredicateState>()
        val state = transform(builder.methodRawFullState()) {
            +MethodFunctionalInliner(psa) {
                if (calledMethod == method) skip()
                val instruction = psa.builder(method).findInstructionsForPredicate(predicate)
                        ?: throw IllegalStateException("No instruction for predicate")
                val instructionState = psa.builder(method).getInstructionState(instruction)
                        ?: throw IllegalStateException("No state for call")
                val (refinement, methodState) = getMethodStateAndRefinement()
                val fixedState = fixPathPredicatesOnTopLevelBeforeInlining(methodState)
                val state = ChainState(refinement.allStates().not(), fixedState)
                inline(state)
                val inlinedNegative = prepareForInline(refinement.allStates())
                val withoutCurrentCall = instructionState.filterNot { it == predicate }
                val negativeExecution = ChainState(withoutCurrentCall, inlinedNegative)
                otherExecutionPaths.add(negativeExecution)
            }
        }
        return state to otherExecutionPaths
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

}


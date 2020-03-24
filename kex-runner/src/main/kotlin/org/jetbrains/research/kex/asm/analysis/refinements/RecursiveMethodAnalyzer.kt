package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.state.PredicateStateBuilder
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
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
            recursiveCalls: List<CallPredicate>,
            recursionPaths: PredicateState,
            normalPaths: PredicateState,
            refinementSource: RefinementSource
    ): Refinement {
        val solver = Z3FixpointSolver(cm.type)
        val refinement: PredicateState = try {
            val result = solver.analyzeRecursion(state, recursiveCalls, rootCall, recursionPaths, refinementSource.condition, normalPaths)
            when (result) {
                is FixpointResult.Sat -> result.result.first()
                else -> falseState()
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


    private fun buildMethodState(builder: MethodRefinementSourceAnalyzer): Pair<PredicateState, List<CallPredicate>> {
        val (preparedState, recursiveCallPredicates, otherExecutionPaths) = prepareMethodState(builder)
        val (transformedTopChoices, otherPathRecursiveCalls) = prepareMethodOtherExecutionPaths(otherExecutionPaths)
        var state = when {
            transformedTopChoices.isEmpty() -> preparedState
            else -> ChoiceState(listOf(preparedState) + transformedTopChoices)
        }
        state = transform(state) {
            +IntrinsicAdapter
            +Optimizer()
            +ConstantPropagator
            +BoolTypeAdapter(cm.type)
            +ArrayBoundsAdapter()
            +StateReducer()
            +Optimizer()
        }.let { state -> MemorySpacer(state).apply(state) }
        return state to (recursiveCallPredicates + otherPathRecursiveCalls)
    }

    private fun prepareMethodOtherExecutionPaths(otherExecutionPaths: List<PredicateState>): Pair<List<PredicateState>, List<CallPredicate>> {
        val recursiveCallPredicates = mutableListOf<CallPredicate>()
        val transformedOtherPaths = otherExecutionPaths.map {
            MethodFunctionalInliner(psa) {
                if (calledMethod == method) {
                    recursiveCallPredicates.add(it)
                    skip()
                    return@MethodFunctionalInliner
                }
                val refinement = findRefinement(calledMethod).expanded()
                var methodState = getStateForInlining() ?: BasicState()
                methodState = fixPathPredicatesOnTopLevelBeforeInlining(methodState)
                val state = ChainState(refinement.allStates().not(), methodState)
                inline(state)
            }.apply(it)
        }
        return transformedOtherPaths to recursiveCallPredicates
    }

    private fun prepareMethodState(builder: MethodRefinementSourceAnalyzer): Triple<PredicateState, List<CallPredicate>, List<PredicateState>> {
        val recursiveCallPredicates = mutableListOf<CallPredicate>()
        val otherExecutionPaths = mutableListOf<PredicateState>()
        val state = transform(builder.methodRawFullState()) {
            +MethodFunctionalInliner(psa) {
                if (calledMethod == method) {
                    recursiveCallPredicates.add(it)
                    skip()
                    return@MethodFunctionalInliner
                }
                val instruction = psa.builder(method).findInstructionsForPredicate(it)
                        ?: throw IllegalStateException("No instruction for predicate")
                val instructionState = psa.builder(method).getInstructionState(instruction)
                        ?: throw IllegalStateException("No state for call")
                val refinement = findRefinement(calledMethod).expanded()
                var methodState = getStateForInlining() ?: BasicState()
                methodState = fixPathPredicatesOnTopLevelBeforeInlining(methodState)
                val state = ChainState(refinement.allStates().not(), methodState)
                inline(state)
                val inlinedNegative = prepareForInline(refinement.allStates())
                val withoutCurrentCall = instructionState.filterNot { predicate -> predicate == it }
                val negativeExecution = ChainState(withoutCurrentCall, inlinedNegative)
                otherExecutionPaths.add(negativeExecution)
            }
        }
        return Triple(state, recursiveCallPredicates, otherExecutionPaths)
    }

    private fun findPathsLeadsToRecursion(calls: List<CallInst>, psb: PredicateStateBuilder) = calls
            .mapNotNull { psb.getInstructionState(it) }
            .map {
                MethodFunctionalInliner(psa) {
                    if (calledMethod == method) {
                        skip()
                        return@MethodFunctionalInliner
                    }
                    var state = getStateForInlining() ?: return@MethodFunctionalInliner
                    state = fixPathPredicatesOnTopLevelBeforeInlining(state)
                    inline(state)
                }.apply(it)
            }
            .map { it.path }
            .let { ChoiceState(it) }
            .optimize()

}


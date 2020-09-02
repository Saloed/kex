package org.jetbrains.research.kex.asm.analysis.refinements

import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.state.PredicateStateBuilder
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import ru.spbstu.ktuples.zip

abstract class MethodAnalyzer(val cm: ClassManager, val psa: PredicateStateAnalysis, val refinementsManager: MethodRefinements, val method: Method): RefinementProvider {

    val CallPredicate.calledMethod: Method
        get() = (call as CallTerm).method

    val CallPredicate.instruction: Instruction
        get() = (call as CallTerm).instruction

    abstract fun analyze(): Refinements

    override fun findRefinement(method: Method): Refinements = refinementsManager.getOrComputeRefinement(method)

    open fun inlineRefinements(ignoredCalls: List<CallInst> = emptyList()): Pair<PredicateState, RefinementSources> {
        val calls = MethodCallCollector.calls(cm, method).filterNot { it in ignoredCalls }
        val refinements = calls.map { findRefinement(it.method) }
        val exceptionalPaths = buildRefinementSources(calls, refinements, ignoredCalls)
        val normalPath = buildNormalPaths(calls, refinements)
        return normalPath to exceptionalPaths
    }

    open fun buildMethodState(builder: MethodExecutionPathsAnalyzer, skipInlining: (Method) -> Boolean = { false }): PredicateState {
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
            applyAdapters(this@MethodAnalyzer)
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

    abstract fun MethodFunctionalInliner.TransformationState.getMethodStateAndRefinement(): Pair<Refinements, PredicateState>

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
                val mapping = otherCalls + (call to reft.state)
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
        val builder = psa.builder(method)
        val predicates = calls.map {
            builder.findPredicateForInstruction(it) ?: throw IllegalStateException("No predicate for call $it")
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

    override fun toString() = "Analyzer: $method"

    companion object {
        fun Transformation.applyAdapters(methodAnalyzer: MethodAnalyzer) {
            +Optimizer
            +ConstantPropagator
            +BoolTypeAdapter(methodAnalyzer.cm.type)
            +Optimizer
        }
    }

}
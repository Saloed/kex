package org.jetbrains.research.kex.asm.analysis.refinements

import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.state.PredicateStateBuilder
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import ru.spbstu.ktuples.zip

abstract class MethodAnalyzer(val cm: ClassManager, val psa: PredicateStateAnalysis, val refinementsManager: MethodRefinements, val method: Method) {

    abstract fun analyze(): Refinements

    fun Transformation.applyAdapters() {
        +Optimizer()
        +ConstantPropagator
        +BoolTypeAdapter(cm.type)
        +ArrayBoundsAdapter()
        +Optimizer()
    }

    open fun findRefinement(method: Method): Refinements = refinementsManager.getOrComputeRefinement(method)

    fun inlineRefinements(ignoredCalls: List<CallInst> = emptyList()): Pair<PredicateState, RefinementSources> {
        val calls = MethodCallCollector.calls(cm, method).filterNot { it in ignoredCalls }
        val refinements = calls.map { findRefinement(it.method) }
        val exceptionalPaths = buildRefinementSources(calls, refinements, ignoredCalls)
        val normalPath = buildNormalPaths(calls, refinements)
        return normalPath to exceptionalPaths
    }

    private fun buildRefinementSources(calls: List<CallInst>, refinements: List<Refinements>, ignoredCalls: List<CallInst>): RefinementSources {
        val builder = psa.builder(method)
        val result = arrayListOf<RefinementSource>()
        val refinementMap = calls.zip(refinements).toMap()
        for ((call, refinement) in zip(calls, refinements)) {
            val otherCalls = refinementMap
                    .filterKeys { it != call }
                    .mapValues { it.value.allStates().not() }
            val (state, callInstructions) = nestedMethodCallStates(builder, call)
            for ((criteria, refState) in refinement.expanded().value) {
                val mapping = otherCalls + (call to refState)
                val refSource = buildRefinementSource(criteria, state, mapping, callInstructions, ignoredCalls)
                result.add(refSource)
            }
        }
        return RefinementSources(result).simplify()
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
        return RefinementSource(criteria, resultPath)
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
        return ChoiceState(allInlined).not()
    }

    private fun nestedMethodCallStates(psb: PredicateStateBuilder, call: CallInst): Pair<PredicateState, Map<CallPredicate, CallInst>> {
        val state = (psb.getInstructionState(call) ?: BasicState())
                .filter { it is CallPredicate || it.type == PredicateType.Path() }
        val callPredicates = PredicateCollector.collectIsInstance<CallPredicate>(state)
        val callInstructions = callPredicates.map {
            psb.findInstructionsForPredicate(it) as? CallInst
                    ?: throw IllegalStateException("Cant find instruction for call")
        }
        val callMap = callPredicates.zip(callInstructions).toMap()
        return state to callMap
    }

    override fun toString() = "Analyzer: $method"

}
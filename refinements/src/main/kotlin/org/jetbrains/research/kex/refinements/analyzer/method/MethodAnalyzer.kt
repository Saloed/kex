package org.jetbrains.research.kex.refinements.analyzer.method

import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.refinements.PathConditions
import org.jetbrains.research.kex.refinements.RefinementProvider
import org.jetbrains.research.kex.refinements.Refinements
import org.jetbrains.research.kex.refinements.analyzer.calls.CallInliner
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.memory.MemoryVersioner
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

abstract class MethodAnalyzer(val cm: ClassManager, val psa: PredicateStateAnalysis, val refinementsManager: MethodRefinements, val method: Method) : RefinementProvider {

    val CallPredicate.calledMethod: Method
        get() = (call as CallTerm).method

    val CallPredicate.instruction: Instruction
        get() = (call as CallTerm).instruction

    abstract fun analyze(): Refinements

    override fun findRefinement(method: Method): Refinements = refinementsManager.getOrComputeRefinement(method)

    override fun toString() = "Analyzer: $method"

    fun buildMemoryVersions(state: PredicateState): Pair<PredicateState, MemoryVersionInfo> {
        val versioner = MemoryVersioner()
        val resultState = versioner.apply(state)
        val memoryVersionInfo = versioner.memoryInfo()
        return resultState to memoryVersionInfo
    }

    fun inlineCalls(state: PredicateState, ignore: Set<CallInst> = emptySet()): Pair<PredicateState, Map<CallPredicate, PathConditions>> {
        val inliner = CallInliner(cm, psa, this, ignoreCalls = ignore)
        val statePrepared = inliner.apply(state).optimize()
        return statePrepared to inliner.callPathConditions
    }

    companion object {
        fun Transformation.applyAdapters(methodAnalyzer: MethodAnalyzer) {
            +Optimizer
            +ConstantPropagator
            +BoolTypeAdapter(methodAnalyzer.cm.type)
            +Optimizer
        }
    }
}

package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method

import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.analysis.refinements.RefinementProvider
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.transformer.BoolTypeAdapter
import org.jetbrains.research.kex.state.transformer.ConstantPropagator
import org.jetbrains.research.kex.state.transformer.Optimizer
import org.jetbrains.research.kex.state.transformer.Transformation
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

abstract class MethodAnalyzer(val cm: ClassManager, val psa: PredicateStateAnalysis, val refinementsManager: MethodRefinements, val method: Method) : RefinementProvider {

    val CallPredicate.calledMethod: Method
        get() = (call as CallTerm).method

    val CallPredicate.instruction: Instruction
        get() = (call as CallTerm).instruction

    abstract fun analyze(): Refinements

    override fun findRefinement(method: Method): Refinements = refinementsManager.getOrComputeRefinement(method)

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

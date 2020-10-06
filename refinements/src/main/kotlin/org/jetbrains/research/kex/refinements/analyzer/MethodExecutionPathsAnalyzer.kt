package org.jetbrains.research.kex.refinements.analyzer

import org.jetbrains.research.kex.refinements.RefinementSource
import org.jetbrains.research.kex.refinements.RefinementSources
import org.jetbrains.research.kex.refinements.analyzer.exceptions.ExceptionSource
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.transformer.IntrinsicAdapter
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import org.jetbrains.research.kfg.ir.value.instruction.ReturnInst
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst
import org.jetbrains.research.kfg.visitor.MethodVisitor

class MethodExecutionPathsAnalyzer(override val cm: ClassManager, val psa: PredicateStateAnalysis, val method: Method) : MethodVisitor {
    override fun cleanup() {}
    private val returnInstructions = arrayListOf<ReturnInst>()
    private val throwInstructions = arrayListOf<ThrowInst>()

    val builder = psa.builder(method)

    init {
        visit(method)
    }

    override fun visitReturnInst(inst: ReturnInst) {
        returnInstructions.add(inst)
    }

    override fun visitThrowInst(inst: ThrowInst) {
        throwInstructions.add(inst)
    }

    val isEmpty: Boolean
        get() = returnInstructions.isEmpty() && throwInstructions.isEmpty()

    val throws: List<ThrowInst>
        get() = throwInstructions

    val returns: List<ReturnInst>
        get() = returnInstructions

    fun methodRawFullState(): PredicateState = (returnInstructions + throwInstructions)
            .mapNotNull { builder.getInstructionState(it) }
            .let { ChoiceState(it) }
            .let { IntrinsicAdapter.apply(it) }

}

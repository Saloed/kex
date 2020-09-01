package org.jetbrains.research.kex.asm.analysis.refinements

import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.transformer.IntrinsicAdapter
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CastInst
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import org.jetbrains.research.kfg.ir.value.instruction.ReturnInst
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst
import org.jetbrains.research.kfg.type.Type
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

    private fun getThrowType(inst: ThrowInst): Type = when {
        inst.throwable is CastInst -> (inst.throwable as CastInst).operand.type
        else -> inst.throwable.type
    }

    private fun getRefinementCriteria(inst: Instruction) = when (inst) {
        is ThrowInst -> RefinementCriteria(getThrowType(inst))
        else -> TODO("Unsupported refinement criteria: $inst")
    }

    val isEmpty: Boolean
        get() = returnInstructions.isEmpty() && throwInstructions.isEmpty()

    val normalExecutionPaths: PredicateState by lazy {
        returnInstructions
                .mapNotNull { builder.getInstructionState(it) }
                .map { it.path }
                .let { ChoiceState(it) }
    }

    val exceptionalExecutionPaths: RefinementSources by lazy {
        throwInstructions
                .map { getRefinementCriteria(it) to builder.getInstructionState(it) }
                .filter { it.second != null }
                .map { it.first to it.second!!.path }
                .map { RefinementSource.create(it.first, it.second) }
                .let { RefinementSources.create(it) }
                .simplify()
    }

    fun methodRawFullState(): PredicateState = (returnInstructions + throwInstructions)
            .mapNotNull { builder.getInstructionState(it) }
            .let { ChoiceState(it) }
            .let { IntrinsicAdapter.apply(it) }

}

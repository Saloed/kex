package org.jetbrains.research.kex.asm.state

import com.abdullin.kthelper.algorithm.DominatorTree
import com.abdullin.kthelper.algorithm.DominatorTreeBuilder
import com.abdullin.kthelper.algorithm.GraphTraversal
import com.abdullin.kthelper.collection.queueOf
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import org.jetbrains.research.kfg.ir.value.instruction.PhiInst
import org.jetbrains.research.kfg.ir.value.instruction.ReturnInst
import org.jetbrains.research.kfg.ir.value.instruction.UnreachableInst
import java.util.*

class InvalidPredicateStateError(msg: String) : Exception(msg)

class PredicateStateBuilder(val method: Method) {
    private val blockStates = hashMapOf<BasicBlock, PredicateState>()
    private val instructionStates = hashMapOf<Instruction, PredicateState>()

    private val order = arrayListOf<BasicBlock>()
    private val domTree = DominatorTree<BasicBlock>()
    private val predicateBuilder = PredicateBuilder(method.cm)

    fun init() {
        predicateBuilder.visit(method)
        if (!method.isAbstract && method.isNotEmpty()) {
            val order = GraphTraversal(method).topologicalSort()

            domTree.putAll(DominatorTreeBuilder(method).build())
            this.order.addAll(order)
        }
    }

    val methodState: PredicateState?
        get() = when {
            method.isConstructor -> method.flatten().lastOrNull()?.run { getInstructionState(this) }
            else -> method.flatten().firstOrNull { it is ReturnInst }?.run { getInstructionState(this) }
        }

    fun getInstructionState(inst: Instruction): PredicateState? {
        val state = instructionStates[inst]
        if (state != null) return state

        val active = hashSetOf<BasicBlock>()

        val queue = queueOf<BasicBlock>()
        queue.add(inst.parent)

        while (queue.isNotEmpty()) {
            val current = queue.poll()
            if (current !in active) {
                active.add(current)
                for (predecessor in current.predecessors) {
                    if (!instructionStates.containsKey(predecessor.terminator)) queue.add(predecessor)
                }
            }
        }
        order.filter { it in active }.forEach {
            processBasicBlock(it)
        }
        return instructionStates[inst]
    }

    private fun processBasicBlock(bb: BasicBlock) {
        var inState = getBlockEntryState(bb) ?: return

        for (inst in bb) {
            val predicate = predicateBuilder.predicateMap[inst]
            val instState = when {
                predicate != null -> (inState.builder() + predicate).apply()
                else -> inState
            }
            instructionStates[inst] = instState

            inState = instState
        }

        blockStates[bb] = inState
    }

    private fun getBlockEntryState(bb: BasicBlock): PredicateState? {
        if (bb in method.catchBlocks) throw InvalidPredicateStateError("Cannot build predicate state for catch block")

        val idom = domTree[bb]?.idom ?: return emptyState()

        val base = blockStates[idom.value] ?: return null
        val choices = mutableListOf<PredicateState>()

        for (predecessor in bb.predecessors) {
            val predState = blockStates[predecessor]?.builder() ?: continue

            val terminatorPredicate = predicateBuilder.terminatorPredicateMap[bb to predecessor.terminator]
            if (terminatorPredicate != null) predState += terminatorPredicate

            for (phi in bb.instructions.mapNotNull { it as? PhiInst }) {
                predState += predicateBuilder.phiPredicateMap.getValue(predecessor to phi)
            }

            val sliced = predState.apply().sliceOn(base)
                    ?: throw InvalidPredicateStateError("Cannot slice predicate state on it's predecessor")
            choices.add(sliced)
        }

        return when {
            choices.isEmpty() -> null
            choices.size == 1 -> base + choices.first()
            else -> base + choices
        }
    }


    fun findInstructionsForPredicate(predicate: Predicate): Instruction? =
            predicateBuilder.predicateMap.inverse[predicate]
}

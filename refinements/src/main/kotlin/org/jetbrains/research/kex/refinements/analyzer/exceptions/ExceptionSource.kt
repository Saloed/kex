package org.jetbrains.research.kex.refinements.analyzer.exceptions

import org.jetbrains.research.kex.refinements.PathConditions
import org.jetbrains.research.kex.refinements.RefinementCriteria
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.trueState
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.ir.value.instruction.CastInst
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst
import org.jetbrains.research.kfg.type.Type

sealed class ExceptionSource {
    abstract val path: PathConditions
    abstract val instruction: Instruction

    abstract fun criteria(): Set<RefinementCriteria>

    data class MethodException(override val instruction: ThrowInst) : ExceptionSource() {
        val refinementCriteria: RefinementCriteria
            get() = RefinementCriteria(getThrowType())

        override val path: PathConditions by lazy {
            PathConditions(mapOf(refinementCriteria to trueState()))
        }

        private fun getThrowType(): Type = when (instruction.throwable) {
            is CastInst -> (instruction.throwable as CastInst).operand.type
            else -> instruction.throwable.type
        }

        override fun criteria() = setOf(refinementCriteria)

        override fun toString(): String = "MethodException: ${instruction.hashCode()}"
    }

    data class CallException(val call: CallPredicate, override val path: PathConditions) : ExceptionSource() {
        override val instruction: Instruction
            get() = call.callTerm.instruction

        override fun criteria() = path.pc.keys

        override fun toString(): String = "CallException: $call"
    }

    data class RecursiveCallException(
            override val instruction: CallInst,
            val criteria: Set<RefinementCriteria>,
            private val callIsException: Boolean = true
    ) : ExceptionSource() {
        override val path = PathConditions(criteria.associateWith { if (callIsException) trueState() else falseState() })
        override fun criteria() = criteria
        override fun toString(): String = "RecursiveCall: $instruction"
    }
}

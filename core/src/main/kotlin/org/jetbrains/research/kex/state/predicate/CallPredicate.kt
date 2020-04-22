package org.jetbrains.research.kex.state.predicate

import com.abdullin.kthelper.assert.asserted
import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.ContextualSerialization
import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.Location
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

@InheritorOf("Predicate")
@Serializable
class CallPredicate(
        val lhvUnsafe: Term?,
        val callTerm: Term,
        @Required override val type: PredicateType = PredicateType.State(),
        @Required @ContextualSerialization override val location: Location = Location(),
        @ContextualSerialization val instruction: Instruction? = null) : Predicate() {

    val hasLhv by lazy { lhvUnsafe != null }
    override val operands by lazy { listOfNotNull(lhvUnsafe, callTerm) }

    constructor(callTerm: Term, type: PredicateType = PredicateType.State(), location: Location = Location())
            : this(null, callTerm, type, location)

    val lhv: Term
        get() = asserted(hasLhv) { operands[0] }

    val call: Term
        get() = if (hasLhv) operands[1] else operands[0]

    fun withInstructionInfo(instruction: Instruction?) = CallPredicate(lhvUnsafe, callTerm, type, location, instruction)

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate {
        val tlhv = if (hasLhv) t.transform(lhv) else null
        val tcall = t.transform(call)
        return when {
            hasLhv -> when {
                tlhv == lhv && tcall == call -> this
                else -> predicate(type, location) { tlhv!!.call(tcall).withInstructionInfo(instruction) }
            }
            else -> when (tcall) {
                call -> this
                else -> predicate(type, location) { call(tcall).withInstructionInfo(instruction) }
            }
        }
    }

    override fun print(): String {
        val sb = StringBuilder()
        if (hasLhv) sb.append("$lhv = ")
        sb.append(call)
        return sb.toString()
    }

    override fun hashCode(): Int = when (instruction) {
        null -> super.hashCode()
        else -> super.hashCode() * 17 + defaultHashCode(instruction)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is CallPredicate) return false
        if (!super.equals(other)) return false
        return when {
            this.instruction != null && other.instruction != null -> this.instruction == other.instruction
            else -> true
        }
    }
}
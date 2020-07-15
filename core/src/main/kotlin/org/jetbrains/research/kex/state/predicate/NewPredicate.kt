package org.jetbrains.research.kex.state.predicate

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
class NewPredicate(
        val lhv: Term,
        @Required @ContextualSerialization val instruction: Instruction,
        @Required override val type: PredicateType = PredicateType.State(),
        @Required @ContextualSerialization override val location: Location = Location()) : Predicate() {
    override val operands by lazy { listOf(lhv) }

    override fun print() = "$lhv = new ${lhv.type}^${instruction.hashCode()}"

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate = when (val tlhv = t.transform(lhv)) {
        lhv -> this
        else -> predicate(type, location) { tlhv.new(instruction) }
    }

    override fun hashCode(): Int = defaultHashCode(super.hashCode(), instruction)
    override fun equals(other: Any?): Boolean = super.equals(other) && instruction == (other as? NewPredicate)?.instruction
}
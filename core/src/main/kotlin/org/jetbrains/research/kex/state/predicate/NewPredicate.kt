package org.jetbrains.research.kex.state.predicate

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.*
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace
import org.jetbrains.research.kfg.ir.Location
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

@InheritorOf("Predicate")
@Serializable
class NewPredicate(
        val lhv: Term,
        @Required @Polymorphic val instruction: Instruction,
        @Required override val type: PredicateType = PredicateType.State(),
        @Required @Contextual override val location: Location = Location()) : Predicate(), NewObjectPredicate {
    override val operands by lazy { listOf(lhv) }
    override val identifier: NewObjectIdentifier
        get() = NewPredicateIdentifier(instruction, lhv.type, lhv.memspace)

    override fun print() = "$lhv = new ${lhv.type}^${instruction.hashCode()}"

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate = when (val tlhv = t.transform(lhv)) {
        lhv -> this
        else -> predicate(type, location) { tlhv.new(instruction) }
    }

    override fun hashCode(): Int = defaultHashCode(super.hashCode(), instruction)
    override fun equals(other: Any?): Boolean = super.equals(other) && instruction == (other as? NewPredicate)?.instruction
}

@Serializable
data class NewPredicateIdentifier(@Polymorphic val instruction: Instruction, override val type: KexType, override val memspace: Int) : NewObjectIdentifier {
    override fun size(sizeFactory: (KexType) -> Int, defaultSize: Int): Int = sizeFactory(type)
}

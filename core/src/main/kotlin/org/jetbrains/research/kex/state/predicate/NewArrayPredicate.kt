package org.jetbrains.research.kex.state.predicate

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.*
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.Location
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

@InheritorOf("Predicate")
@Serializable
class NewArrayPredicate(
        val lhv: Term,
        val dimentions: List<Term>,
        val elementType: KexType,
        @Required @Polymorphic val instruction: Instruction,
        @Required override val type: PredicateType = PredicateType.State(),
        @Required @Contextual override val location: Location = Location()) : Predicate() {
    override val operands by lazy { listOf(lhv) + dimentions }

    val numDimentions: Int
        get() = dimentions.size

    override fun print(): String {
        val sb = StringBuilder()
        sb.append("$lhv = new $elementType")
        dimentions.forEach { sb.append("[$it]") }
        sb.append("^${instruction.hashCode()}")
        return sb.toString()
    }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate {
        val tlhv = t.transform(lhv)
        val tdimentions = dimentions.map { t.transform(it) }
        return when {
            tlhv == lhv && tdimentions == dimentions -> this
            else -> predicate(type, location) { tlhv.new(tdimentions, instruction) }
        }
    }

    override fun hashCode(): Int = defaultHashCode(super.hashCode(), instruction)
    override fun equals(other: Any?): Boolean = super.equals(other) && instruction == (other as? NewArrayPredicate)?.instruction
}
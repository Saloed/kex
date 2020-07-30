package org.jetbrains.research.kex.state.predicate

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.*
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexArray
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.term.ConstIntTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace
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
        @Required @Contextual override val location: Location = Location()) : Predicate(), NewObjectPredicate {
    override val operands by lazy { listOf(lhv) + dimentions }

    override val identifier: NewObjectIdentifier
        get() = NewArrayPredicateIdentifier(instruction, elementType, lhv.memspace).also { it.dimensions = dimentions }

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

@Serializable
data class NewArrayPredicateIdentifier(@Polymorphic val instruction: Instruction, val elementType: KexType, override val memspace: Int) : NewObjectIdentifier {
    lateinit var dimensions: List<Term>
    override val type: KexType
        get() = KexArray(elementType, memspace)

    override fun size(sizeFactory: (KexType) -> Int, defaultSize: Int): Int {
        val elementSize = sizeFactory(elementType)
        val length = dimensions.fold(1) { acc: Int, term: Term ->
            acc * ((term as? ConstIntTerm)?.value ?: defaultSize)
        }
        return elementSize * length
    }
}

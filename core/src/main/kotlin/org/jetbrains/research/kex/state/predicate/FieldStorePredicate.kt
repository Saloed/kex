package org.jetbrains.research.kex.state.predicate

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Contextual
import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexReference
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.MemoryAccess
import org.jetbrains.research.kex.state.memory.MemoryAccessType
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.term.FieldTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace
import org.jetbrains.research.kfg.ir.Location

@InheritorOf("Predicate")
@Serializable
class FieldStorePredicate(
        val field: Term,
        val value: Term,
        @Required override val type: PredicateType = PredicateType.State(),
        @Required @Contextual override val location: Location = Location(),
        override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Predicate(), MemoryAccess<FieldStorePredicate> {
    override val operands by lazy { listOf(this.field, this.value) }

    override val memoryType: MemoryType = MemoryType.PROPERTY
    override val accessType: MemoryAccessType = MemoryAccessType.WRITE
    override val memorySpace: Int
        get() = this.field.memspace
    override val memoryName: String
        get() = "${(this.field as FieldTerm).klass}.${this.field.fieldNameString}"
    override val memoryValueType: KexType
        get() = (this.field.type as KexReference).reference

    override fun print() = "*($field) = $value"

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate {
        val tfield = t.transform(field)
        val tvalue = t.transform(value)
        return when {
            tfield == field && tvalue == value -> this
            else -> FieldStorePredicate(tfield, tvalue, type, location, memoryVersion)
        }
    }

    override fun withMemoryVersion(memoryVersion: MemoryVersion) = FieldStorePredicate(field, value, type, location, memoryVersion)

    override fun equals(other: Any?) = super.equals(other) && memoryEquals(other)
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryHash())
}

package org.jetbrains.research.kex.state.predicate

import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.defaultHashCode
import com.abdullin.kthelper.logging.log
import kotlinx.serialization.Contextual
import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexArray
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.MemoryAccess
import org.jetbrains.research.kex.state.memory.MemoryAccessType
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.term.ArrayLoadTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace
import org.jetbrains.research.kfg.ir.Location

@InheritorOf("Predicate")
@Serializable
class ArrayStorePredicate(
        val arrayRef: Term,
        val value: Term,
        @Required override val type: PredicateType = PredicateType.State(),
        @Required @Contextual override val location: Location = Location(),
        override val memoryVersion: MemoryVersion = MemoryVersion.default(),
        override val additionalInfo: String = "") : Predicate(), MemoryAccess<ArrayStorePredicate> {
    override val operands by lazy { listOf(arrayRef, value) }

    val componentType: KexType
        get() = (arrayRef.type as? KexArray)?.element ?: unreachable { log.error("Non-array type of array ref") }

    override fun print() = "*($arrayRef) = $value"

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate {
        val ref = t.transform(arrayRef)
        val store = t.transform(value)
        return when {
            ref == arrayRef && store == value -> this
            else -> ArrayStorePredicate(ref, store, type, location, memoryVersion, additionalInfo)
        }
    }

    override val accessType: MemoryAccessType = MemoryAccessType.WRITE
    override val memoryType: MemoryType = MemoryType.ARRAY
    override val memoryName: String = ArrayLoadTerm.ARRAY_MEMORY_NAME
    override val memorySpace: Int
        get() = arrayRef.memspace
    override val memoryValueType: KexType
        get() = componentType

    override fun withMemoryVersion(memoryVersion: MemoryVersion) = ArrayStorePredicate(arrayRef, value, type, location, memoryVersion, additionalInfo)
    override fun withAdditionalInfo(additionalInfo: String) = ArrayStorePredicate(arrayRef, value, type, location, memoryVersion, additionalInfo)
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryHash())
    override fun equals(other: Any?) = super.equals(other) && memoryEquals(other)
}
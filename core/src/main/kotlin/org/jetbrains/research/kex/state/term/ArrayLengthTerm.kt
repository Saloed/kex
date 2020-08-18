package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.MemoryAccess
import org.jetbrains.research.kex.state.memory.MemoryAccessType
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace

@InheritorOf("Term")
@Serializable
class ArrayLengthTerm(
        override val type: KexType,
        val arrayRef: Term,
        override val memoryVersion: MemoryVersion = MemoryVersion.default(),
        override val additionalInfo: String = "") : Term(), MemoryAccess<ArrayLengthTerm> {
    override val name = "$arrayRef.length"
    override val subterms by lazy { listOf(arrayRef) }

    override val memoryType: MemoryType = MemoryType.SPECIAL
    override val accessType: MemoryAccessType = MemoryAccessType.READ
    override val memorySpace: Int
        get() = arrayRef.memspace
    override val memoryName: String = ARRAY_LENGTH_MEMORY_NAME
    override val memoryValueType: KexType = KexInt()

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val tarrayRef = t.transform(arrayRef)) {
                arrayRef -> this
                else -> ArrayLengthTerm(KexInt(), tarrayRef, memoryVersion, additionalInfo)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion) = ArrayLengthTerm(type, arrayRef, memoryVersion, additionalInfo)
    override fun withAdditionalInfo(additionalInfo: String) = ArrayLengthTerm(type, arrayRef, memoryVersion, additionalInfo)

    override fun equals(other: Any?) = super.equals(other) && memoryEquals(other)
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryHash())

    companion object {
        const val ARRAY_LENGTH_MEMORY_NAME = "__ARRAY_LENGTH__"
    }
}
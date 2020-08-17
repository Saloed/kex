package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.MemoryAccess
import org.jetbrains.research.kex.state.memory.MemoryAccessType
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace

@InheritorOf("Term")
@Serializable
class ArrayLoadTerm(override val type: KexType, val arrayRef: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryAccess<ArrayLoadTerm> {
    override val name = "*($arrayRef)"
    override val subterms by lazy { listOf(arrayRef) }
    override val memoryType: MemoryType = MemoryType.ARRAY
    override val accessType: MemoryAccessType = MemoryAccessType.READ
    override val memoryName: String = ARRAY_MEMORY_NAME
    override val memoryValueType: KexType
        get() = type
    override val memorySpace: Int
        get() = arrayRef.memspace

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val tarrayRef = t.transform(arrayRef)) {
                arrayRef -> this
                else -> ArrayLoadTerm(type, tarrayRef, memoryVersion)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion): ArrayLoadTerm = ArrayLoadTerm(type, arrayRef, memoryVersion)

    override fun equals(other: Any?) = super.equals(other) && memoryEquals(other)
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryHash())
    companion object{
        const val ARRAY_MEMORY_NAME = "Array"
    }
}

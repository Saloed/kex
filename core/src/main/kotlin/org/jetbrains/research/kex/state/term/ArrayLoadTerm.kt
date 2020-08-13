package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class ArrayLoadTerm(override val type: KexType, val arrayRef: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val name = "*($arrayRef)"
    override val subterms by lazy { listOf(arrayRef) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val tarrayRef = t.transform(arrayRef)) {
                arrayRef -> this
                else -> ArrayLoadTerm(type, tarrayRef, memoryVersion)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ArrayLoadTerm(type, arrayRef, memoryVersion)

    override fun equals(other: Any?) = super.equals(other) && memoryVersion == (other as? MemoryDependentTerm)?.memoryVersion
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryVersion)
}
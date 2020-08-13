package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class ArrayIndexTerm(override val type: KexType, val arrayRef: Term, val index: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val name = "$arrayRef[$index]"
    override val subterms by lazy { listOf(arrayRef, index) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term {
        val tarrayRef = t.transform(arrayRef)
        val tindex = t.transform(index)
        return when {
            tarrayRef == arrayRef && tindex == index -> this
            else -> ArrayIndexTerm(type, tarrayRef, tindex, memoryVersion)
        }
    }

    override fun equals(other: Any?) = super.equals(other) && memoryVersion == (other as? MemoryDependentTerm)?.memoryVersion
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryVersion)

    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ArrayIndexTerm(type, arrayRef, index, memoryVersion)
}
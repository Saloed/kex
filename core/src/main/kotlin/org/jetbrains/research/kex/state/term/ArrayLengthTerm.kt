package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class ArrayLengthTerm(override val type: KexType, val arrayRef: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val name = "$arrayRef.length"
    override val subterms by lazy { listOf(arrayRef) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val tarrayRef = t.transform(arrayRef)) {
                arrayRef -> this
                else -> ArrayLengthTerm(KexInt(), tarrayRef, memoryVersion)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ArrayLengthTerm(type, arrayRef, memoryVersion)

    override fun equals(other: Any?) = super.equals(other) && memoryVersion == (other as? MemoryDependentTerm)?.memoryVersion
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryVersion)
}
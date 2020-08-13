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
class BoundTerm(override val type: KexType, val ptr: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val name = "bound($ptr)"
    override val subterms by lazy { listOf(ptr) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val nptr = t.transform(ptr)) {
                ptr -> this
                else -> BoundTerm(KexInt(), nptr, memoryVersion)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = BoundTerm(type, ptr, memoryVersion)

    override fun equals(other: Any?) = super.equals(other) && memoryVersion == (other as? MemoryDependentTerm)?.memoryVersion
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryVersion)
}
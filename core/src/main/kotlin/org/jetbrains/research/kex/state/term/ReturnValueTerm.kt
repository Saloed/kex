package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Contextual
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.Method

@InheritorOf("Term")
@Serializable
class ReturnValueTerm(
        override val type: KexType,
        @Contextual val method: Method,
        override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val name = "<retval>"
    override val subterms by lazy { listOf<Term>() }

    override fun <T : Transformer<T>> accept(t: Transformer<T>) = this
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ReturnValueTerm(type, method, memoryVersion)

    override fun equals(other: Any?) = super.equals(other) && memoryVersion == (other as? MemoryDependentTerm)?.memoryVersion
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryVersion)
}
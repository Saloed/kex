package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class ArgumentTerm(override val type: KexType, val index: Int, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term() {
    override val name = "arg$$index"
    override val subterms by lazy { listOf<Term>() }

    override fun <T: Transformer<T>> accept(t: Transformer<T>) = this
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ArgumentTerm(type, index, memoryVersion)

    override fun hashCode() = defaultHashCode(index, super.hashCode())
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (this.javaClass != other?.javaClass) return false
        other as ArgumentTerm
        return this.index == other.index && super.equals(other)
    }
}
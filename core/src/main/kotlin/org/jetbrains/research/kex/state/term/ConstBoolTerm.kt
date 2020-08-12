package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class ConstBoolTerm(val value: Boolean, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term() {
    override val name = value.toString()
    override val type: KexType = KexBool()
    override val subterms by lazy { listOf<Term>() }

    override fun <T: Transformer<T>> accept(t: Transformer<T>) = this
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ConstBoolTerm(value, memoryVersion)
}
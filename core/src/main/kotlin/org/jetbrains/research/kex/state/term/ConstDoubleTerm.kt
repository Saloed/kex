package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexDouble
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class ConstDoubleTerm(val value: Double, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term() {
    override val name = value.toString()
    override val type: KexType = KexDouble()
    override val subterms by lazy { listOf<Term>() }

    override fun <T: Transformer<T>> accept(t: Transformer<T>) = this
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ConstDoubleTerm(value, memoryVersion)
}
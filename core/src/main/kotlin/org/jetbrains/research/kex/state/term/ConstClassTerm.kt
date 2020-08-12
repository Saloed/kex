package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Contextual
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.Class

@InheritorOf("Term")
@Serializable
class ConstClassTerm(
        override val type: KexType,
        @Contextual val `class`: Class,
        override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term() {
    override val name = "$`class`.class"
    override val subterms by lazy { listOf<Term>() }

    override fun <T: Transformer<T>> accept(t: Transformer<T>) = this
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ConstClassTerm(type, `class`, memoryVersion)
}
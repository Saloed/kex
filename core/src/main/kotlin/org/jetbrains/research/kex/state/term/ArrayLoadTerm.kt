package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class ArrayLoadTerm(override val type: KexType, val arrayRef: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term() {
    override val name = "*($arrayRef)"
    override val subterms by lazy { listOf(arrayRef) }

    override fun <T: Transformer<T>> accept(t: Transformer<T>): Term =
            when (val tarrayRef = t.transform(arrayRef)) {
                arrayRef -> this
                else -> term { tf.getArrayLoad(type, tarrayRef) }
            }
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = ArrayLoadTerm(type, arrayRef, memoryVersion)
}
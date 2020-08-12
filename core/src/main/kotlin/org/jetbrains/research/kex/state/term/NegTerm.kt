package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class NegTerm(override val type: KexType, val operand: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term() {
    override val name = "-$operand"
    override val subterms by lazy { listOf(operand) }

    override fun <T: Transformer<T>> accept(t: Transformer<T>): Term =
            when (val toperand = t.transform(operand)) {
                operand -> this
                else -> term { tf.getNegTerm(toperand) }
             }
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = NegTerm(type, operand, memoryVersion)
}
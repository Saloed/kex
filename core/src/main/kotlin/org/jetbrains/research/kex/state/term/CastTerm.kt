package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class CastTerm(override val type: KexType, val operand: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val name = "($operand as $type)"
    override val subterms by lazy { listOf(operand) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val toperand = t.transform(operand)) {
                operand -> this
                else -> CastTerm(type, toperand, memoryVersion)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = CastTerm(type, operand, memoryVersion)

    override fun equals(other: Any?) = super.equals(other) && memoryVersion == (other as? MemoryDependentTerm)?.memoryVersion
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryVersion)
}
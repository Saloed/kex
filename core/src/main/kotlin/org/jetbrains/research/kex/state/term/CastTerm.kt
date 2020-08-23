package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.*
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class CastTerm(
        override val type: KexType,
        val operand: Term,
        override val memoryVersion: MemoryVersion = MemoryVersion.default(),
        override val scopeInfo: MemoryAccessScope = MemoryAccessScope.RootScope) : Term(), MemoryAccess<CastTerm> {
    override val name = "($operand as $type)"
    override val subterms by lazy { listOf(operand) }

    override val memoryType: MemoryType = MemoryType.SPECIAL
    override val accessType: MemoryAccessType = MemoryAccessType.WRITE
    override val memorySpace: Int = 0
    override val memoryName: String = InstanceOfTerm.TYPE_MEMORY_NAME
    override val memoryValueType: KexType = KexInt()

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val toperand = t.transform(operand)) {
                operand -> this
                else -> CastTerm(type, toperand, memoryVersion, scopeInfo)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion) = CastTerm(type, operand, memoryVersion, scopeInfo)
    override fun withScopeInfo(scopeInfo: MemoryAccessScope) = CastTerm(type, operand, memoryVersion, scopeInfo)

    override fun equals(other: Any?) = super.equals(other) && memoryEquals(other)
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryHash())
    override fun toString(): String = "$name #${memoryPrint()}"
}
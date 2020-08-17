package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.MemoryAccess
import org.jetbrains.research.kex.state.memory.MemoryAccessType
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class InstanceOfTerm(val checkedType: KexType, val operand: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryAccess<InstanceOfTerm> {
    override val name = "$operand instanceof $checkedType"
    override val type: KexType = KexBool()
    override val subterms by lazy { listOf(operand) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val toperand = t.transform(operand)) {
                operand -> this
                else -> InstanceOfTerm(checkedType, toperand, memoryVersion)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion) = InstanceOfTerm(checkedType, operand, memoryVersion)

    override fun hashCode() = defaultHashCode(super.hashCode(), checkedType, memoryHash())
    override fun equals(other: Any?): Boolean {
        if (other?.javaClass != this.javaClass) return false
        other as InstanceOfTerm
        return super.equals(other) && this.checkedType == other.checkedType && memoryEquals(other)
    }

    override val memoryType: MemoryType = MemoryType.SPECIAL
    override val accessType: MemoryAccessType = MemoryAccessType.READ
    override val memorySpace: Int = 0
    override val memoryName: String = TYPE_MEMORY_NAME
    override val memoryValueType: KexType = KexInt()

    companion object {
        const val TYPE_MEMORY_NAME = "__TYPE__"
    }
}
package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class InstanceOfTerm(val checkedType: KexType, val operand: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val name = "$operand instanceof $checkedType"
    override val type: KexType = KexBool()
    override val subterms by lazy { listOf(operand) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val toperand = t.transform(operand)) {
                operand -> this
                else -> InstanceOfTerm(checkedType, toperand, memoryVersion)
            }

    override fun hashCode() = defaultHashCode(super.hashCode(), checkedType, memoryVersion)
    override fun equals(other: Any?): Boolean {
        if (other?.javaClass != this.javaClass) return false
        other as InstanceOfTerm
        return super.equals(other) && this.checkedType == other.checkedType && this.memoryVersion == other.memoryVersion
    }

    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = InstanceOfTerm(checkedType, operand, memoryVersion)
}
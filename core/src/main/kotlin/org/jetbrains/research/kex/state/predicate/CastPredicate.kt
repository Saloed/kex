package org.jetbrains.research.kex.state.predicate

import org.jetbrains.research.kthelper.defaultHashCode
import kotlinx.serialization.Contextual
import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.*
import org.jetbrains.research.kex.state.term.InstanceOfTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.Location

@InheritorOf("Predicate")
@Serializable
class CastPredicate(
        val lhv: Term,
        val operand: Term,
        val operandType: KexType,
        @Required override val type: PredicateType = PredicateType.State(),
        @Required @Contextual override val location: Location = Location(),
        override val memoryVersion: MemoryVersion = MemoryVersion.default(),
        override val scopeInfo: MemoryAccessScope = MemoryAccessScope.RootScope) : Predicate(), MemoryAccess<CastPredicate> {

    override val operands by lazy { listOf(lhv, operand) }

    override val memoryType: MemoryType = MemoryType.SPECIAL
    override val accessType: MemoryAccessType = MemoryAccessType.WRITE
    override val memorySpace: Int = 0
    override val memoryName: String = InstanceOfTerm.TYPE_MEMORY_NAME
    override val memoryValueType: KexType = KexInt()

    override fun print() = "$lhv = ($operand as $operandType)  #${memoryPrint()}"

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate {
        val tlhv = t.transform(lhv)
        val toperand = t.transform(operand)
        return when {
            tlhv == lhv && toperand == operand -> this
            else -> CastPredicate(tlhv, toperand, operandType, type, location, memoryVersion, scopeInfo)
        }
    }

    override fun withMemoryVersion(memoryVersion: MemoryVersion) = CastPredicate(lhv, operand, operandType, type, location, memoryVersion, scopeInfo)
    override fun withScopeInfo(scopeInfo: MemoryAccessScope) = CastPredicate(lhv, operand, operandType, type, location, memoryVersion, scopeInfo)

    override fun equals(other: Any?) = super.equals(other) && memoryEquals(other)
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryHash())
}

package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.*
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class FieldMemoryTerm(
    override val type: KexType,
    val fieldClass: String,
    val fieldName: String,
    override val memorySpace: Int,
    override val memoryVersion: MemoryVersion = MemoryVersion.default(),
    override val scopeInfo: MemoryAccessScope = MemoryAccessScope.RootScope
) : Term(), MemoryAccess<FieldMemoryTerm> {
    override val name = "*#(${fieldClass}.${fieldName})"
    override val subterms by lazy { emptyList<Term>() }

    override val accessType: MemoryAccessType = MemoryAccessType.READ
    override val memoryType: MemoryType = MemoryType.PROPERTY
    override val memoryName: String
        get() = "${fieldClass}.${fieldName}"
    override val memoryValueType: KexType
        get() = type

    override fun <T : Transformer<T>> accept(t: Transformer<T>) =
        FieldMemoryTerm(type, fieldClass, fieldName, memorySpace, memoryVersion, scopeInfo)

    override fun withMemoryVersion(memoryVersion: MemoryVersion) =
        FieldMemoryTerm(type, fieldClass, fieldName, memorySpace, memoryVersion, scopeInfo)

    override fun withScopeInfo(scopeInfo: MemoryAccessScope) =
        FieldMemoryTerm(type, fieldClass, fieldName, memorySpace, memoryVersion, scopeInfo)

    override fun hashCode() = defaultHashCode(super.hashCode(), memoryHash())
    override fun equals(other: Any?) = super.equals(other) && memoryEquals(other)
    override fun toString(): String = "$name #${memoryPrint()}"
}

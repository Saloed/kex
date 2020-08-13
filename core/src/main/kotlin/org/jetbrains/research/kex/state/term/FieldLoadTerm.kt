package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.defaultHashCode
import com.abdullin.kthelper.logging.log
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class FieldLoadTerm(override val type: KexType, val field: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val name = "*($field)"
    override val subterms by lazy { listOf(this.field) }

    val isStatic
        get() = (field as? FieldTerm)?.isStatic ?: unreachable { log.error("Non-field term in field load") }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val tfield = t.transform(field)) {
                field -> this
                else -> FieldLoadTerm(type, tfield, memoryVersion)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = FieldLoadTerm(type, field, memoryVersion)

    override fun equals(other: Any?) = super.equals(other) && memoryVersion == (other as? MemoryDependentTerm)?.memoryVersion
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryVersion)
}
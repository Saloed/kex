package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.defaultHashCode
import com.abdullin.kthelper.logging.log
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryAccess
import org.jetbrains.research.kex.state.MemoryAccessType
import org.jetbrains.research.kex.state.MemoryType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace

@InheritorOf("Term")
@Serializable
class FieldLoadTerm(override val type: KexType, val field: Term, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryAccess<FieldLoadTerm> {
    override val name = "*($field)"
    override val subterms by lazy { listOf(this.field) }

    override val accessType: MemoryAccessType = MemoryAccessType.READ
    override val memoryType: MemoryType = MemoryType.CLASS_PROPERTY
    override val memorySpace: Int
        get() = this.field.memspace
    override val memoryName: String
        get() = "${(this.field as FieldTerm).klass}.${this.field.fieldNameString}"

    val isStatic
        get() = (field as? FieldTerm)?.isStatic ?: unreachable { log.error("Non-field term in field load") }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val tfield = t.transform(field)) {
                field -> this
                else -> FieldLoadTerm(type, tfield, memoryVersion)
            }

    override fun withMemoryVersion(memoryVersion: MemoryVersion) = FieldLoadTerm(type, field, memoryVersion)

    override fun hashCode() = defaultHashCode(super.hashCode(), memoryHash())
    override fun equals(other: Any?) = super.equals(other) && memoryEquals(other)
}
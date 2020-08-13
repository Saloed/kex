package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.predicate.NewObjectIdentifier
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
data class LocalObjectTerm(val id: String, val identifier: NewObjectIdentifier, override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), MemoryDependentTerm {
    override val type: KexType
        get() = identifier.type
    override val name = id
    override val subterms: List<Term> = emptyList()
    override fun <T : Transformer<T>> accept(t: Transformer<T>) = this
    override fun toString(): String = "${id}^${identifier.hashCode()}"
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = LocalObjectTerm(id, identifier, memoryVersion)
}

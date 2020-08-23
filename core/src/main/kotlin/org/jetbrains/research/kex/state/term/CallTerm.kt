package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Contextual
import kotlinx.serialization.Polymorphic
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.ElementWithMemoryVersion
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

@InheritorOf("Term")
@Serializable
class CallTerm(
        override val type: KexType,
        val owner: Term,
        @Contextual val method: Method,
        @Polymorphic val instruction: Instruction,
        val arguments: List<Term>,
        override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term(), ElementWithMemoryVersion<CallTerm> {
    override val name = "$owner.${method.name}(${arguments.joinToString()})^${instruction.hashCode()}"
    override val subterms by lazy { listOf(owner) + arguments }

    val isStatic: Boolean
        get() = owner is ConstClassTerm

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term {
        val towner = t.transform(owner)
        val targuments = arguments.map { t.transform(it) }
        return when {
            towner == owner && targuments == arguments -> this
            else -> CallTerm(type, towner, method, instruction, targuments, memoryVersion)
        }
    }

    override fun withMemoryVersion(memoryVersion: MemoryVersion) = CallTerm(type, owner, method, instruction, arguments, memoryVersion)
    override fun hashCode() = defaultHashCode(super.hashCode(), memoryVersion)
    override fun equals(other: Any?) = super.equals(other) &&  memoryVersion == (other as? CallTerm)?.memoryVersion
    override fun toString(): String = "$name #${memoryVersion.humanReadableName}"
}

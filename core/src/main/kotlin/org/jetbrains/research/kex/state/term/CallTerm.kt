package org.jetbrains.research.kex.state.term

import kotlinx.serialization.ContextualSerialization
import kotlinx.serialization.Polymorphic
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

@InheritorOf("Term")
@Serializable
class CallTerm(
        override val type: KexType,
        val owner: Term,
        @ContextualSerialization val method: Method,
        @Polymorphic val instruction: Instruction,
        val arguments: List<Term>) : Term() {
    override val name = "$owner.${method.name}(${arguments.joinToString()})^${instruction.hashCode()}"
    override val subterms by lazy { listOf(owner) + arguments }

    val isStatic: Boolean
        get() = owner is ConstClassTerm

    override fun <T: Transformer<T>> accept(t: Transformer<T>): Term {
        val towner = t.transform(owner)
        val targuments = arguments.map { t.transform(it) }
        return when {
            towner == owner && targuments == arguments -> this
            else -> term { tf.getCall(method, instruction, towner, targuments) }
        }
    }
}
package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexPointer
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class PrimitiveCastTerm(override val type: KexType, val operand: Term) : Term() {
    init {
        check(type !is KexPointer && operand.type !is KexPointer) { "Primitive cast supports only primitive types" }
    }

    override val name = "($operand as $type)"
    override val subterms by lazy { listOf(operand) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term =
            when (val toperand = t.transform(operand)) {
                operand -> this
                else -> PrimitiveCastTerm(type, toperand)
            }
}
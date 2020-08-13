package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.*
import org.jetbrains.research.kex.ktype.KexByte
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.transformer.Transformer

abstract class ConstValueTerm<T> : Term() {
    abstract val value: T
    override val name: String
        get() = "$value"
    override val subterms by lazy { listOf<Term>() }
    override fun <T : Transformer<T>> accept(t: Transformer<T>) = this
}

@InheritorOf("Term")
@Serializable
class ConstBoolTerm(override val value: Boolean) : ConstValueTerm<Boolean>() {
    override val type: KexType = KexBool()
}

@InheritorOf("Term")
@Serializable
class ConstByteTerm(override val value: Byte) : ConstValueTerm<Byte>() {
    override val type: KexType = KexByte()
}

@InheritorOf("Term")
@Serializable
class ConstCharTerm(override val value: Char) : ConstValueTerm<Char>() {
    override val type: KexType = KexChar()
}

@InheritorOf("Term")
@Serializable
class ConstDoubleTerm(override val value: Double) : ConstValueTerm<Double>() {
    override val type: KexType = KexDouble()
}

@InheritorOf("Term")
@Serializable
class ConstFloatTerm(override val value: Float) : ConstValueTerm<Float>() {
    override val type: KexType = KexFloat()
}

@InheritorOf("Term")
@Serializable
class ConstIntTerm(override val value: Int) : ConstValueTerm<Int>() {
    override val type: KexType = KexInt()
}

@InheritorOf("Term")
@Serializable
class ConstLongTerm(override val value: Long) : ConstValueTerm<Long>() {
    override val type: KexType = KexLong()
}

@InheritorOf("Term")
@Serializable
class ConstShortTerm(override val value: Short) : ConstValueTerm<Short>() {
    override val type: KexType = KexShort()
}

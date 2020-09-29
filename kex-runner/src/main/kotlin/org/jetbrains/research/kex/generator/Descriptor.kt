package org.jetbrains.research.kex.generator

import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.ktype.*
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.predicate.assume
import org.jetbrains.research.kex.state.predicate.require
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kfg.type.ArrayType
import org.jetbrains.research.kfg.ir.Class as KfgClass
import org.jetbrains.research.kfg.type.Type as KfgType

sealed class Descriptor {
    abstract val term: Term
    abstract val type: KexType

    abstract fun toState(ps: PredicateState = emptyState()): PredicateState
}

sealed class ConstantDescriptor : Descriptor() {
    override fun toState(ps: PredicateState) = unreachable<PredicateState> {
        log.error("Can't transform constant descriptor $this to predicate state")
    }

    object Null : ConstantDescriptor() {
        override val type = KexNull()
        override val term = term { const(null) }
        override fun toString() = "null"
    }

    data class Bool(val value: Boolean) : ConstantDescriptor() {
        override val type = KexBool()
        override val term get() = term { const(value) }
    }

    data class Int(val value: kotlin.Int) : ConstantDescriptor() {
        override val type = KexInt()
        override val term get() = term { const(value) }
    }

    data class Long(val value: kotlin.Long) : ConstantDescriptor() {
        override val type = KexLong()
        override val term get() = term { const(value) }
    }

    data class Float(val value: kotlin.Float) : ConstantDescriptor() {
        override val type = KexFloat()
        override val term get() = term { const(value) }
    }

    data class Double(val value: kotlin.Double) : ConstantDescriptor() {
        override val type = KexDouble()
        override val term get() = term { const(value) }
    }

    data class Class(val value: KfgClass) : ConstantDescriptor() {
        override val type = KexClass(value.fullname)
        override val term get() = term { `class`(value) }
    }
}

data class FieldDescriptor(
        val name: String,
        val kfgType: KfgType,
        val klass: KfgClass,
        val owner: Descriptor,
        val value: Descriptor
) : Descriptor() {
    override val type = kfgType.kexType
    override val term = term { owner.term.field(type, name, owner.type as KexClass) }

    override fun toState(ps: PredicateState): PredicateState {
        var state = ps
        if (value !is ConstantDescriptor) {
            state = value.toState(state)
        }
        return state.builder().run {
            val tempTerm = term { generate(this@FieldDescriptor.type) }
            state { tempTerm equality term.load() }
            require { tempTerm equality value.term }
            apply()
        }
    }

    override fun toString() = "${klass.fullname}.$name = $value"
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as FieldDescriptor

        if (name != other.name) return false
        if (type != other.type) return false
        if (klass != other.klass) return false
        if (value != other.value) return false

        return true
    }

    override fun hashCode(): Int {
        var result = name.hashCode()
        result = 31 * result + type.hashCode()
        result = 31 * result + klass.hashCode()
        result = 31 * result + value.hashCode()
        return result
    }
}

data class ObjectDescriptor(
        val klass: KfgClass,
        private val fieldsInner: MutableMap<String, FieldDescriptor> = mutableMapOf()
) : Descriptor() {
    override val term = term { generate(klass.kexType) }
    override val type = KexClass(klass.fullname)
    val name = term.name
    val fields get() = fieldsInner.toMap()

    operator fun set(field: String, value: FieldDescriptor) {
        fieldsInner[field] = value
    }

    operator fun get(field: String) = fieldsInner[field]

    override fun toState(ps: PredicateState): PredicateState {
        var state = ps
        fields.values.forEach {
            state = it.toState(state)
        }
        return state
    }

    override fun toString(): String = buildString {
        append("$klass {")
        if (fieldsInner.isNotEmpty()) {
            append("\n  ")
            appendLine(fieldsInner.values.joinToString("\n").replace("\n", "\n  "))
        }
        appendLine("}")
    }

    fun merge(other: ObjectDescriptor): ObjectDescriptor {
        val fields = fieldsInner.toMutableMap()
        for ((name, desc) in other.fields) {
            when (name) {
                in fields -> {
                    val currentValue = fields[name]
                    if (currentValue != desc) {
                        fields.remove(name)
                    }
                }
                else -> fields += name to desc
            }
        }
        return ObjectDescriptor(klass, fields)
    }
}

data class ArrayDescriptor(
        val length: Int,
        val kfgType: KfgType,
        private val elementsInner: MutableMap<Int, Descriptor> = mutableMapOf()
) : Descriptor() {
    val elementType = (kfgType as ArrayType).component
    override val type = KexArray(elementType.kexType)
    override val term = term { generate(type) }
    val name = term.name
    val elements get() = elementsInner.toMap()

    operator fun set(index: Int, value: Descriptor) {
        elementsInner[index] = value
    }

    override fun toState(ps: PredicateState): PredicateState {
        var state = ps
        elements.forEach { (index, element) ->
            state = element.toState(state)
            state += require { term[index] equality element.term }
        }
        return state
    }

    override fun toString(): String = buildString {
        append("$type {")
        if (elementsInner.isNotEmpty()) {
            append("\n  ")
            appendLine(elementsInner.toList().joinToString("\n") { "[${it.first}] = ${it.second}" }.replace("\n", "\n  "))
        }
        appendLine("}")
    }
}

class DescriptorBuilder(val context: ExecutionContext) {
    val `null` = ConstantDescriptor.Null
    fun const(@Suppress("UNUSED_PARAMETER") nothing: Nothing?) = `null`
    fun const(value: Boolean) = ConstantDescriptor.Bool(value)
    fun const(number: Number) = when (number) {
        is Long -> ConstantDescriptor.Long(number)
        is Float -> ConstantDescriptor.Float(number)
        is Double -> ConstantDescriptor.Double(number)
        else -> ConstantDescriptor.Int(number.toInt())
    }

    fun `object`(type: KfgClass): ObjectDescriptor = ObjectDescriptor(type)
    fun array(length: Int, type: KfgType): ArrayDescriptor = ArrayDescriptor(length, type)

    fun ObjectDescriptor.field(name: String, type: KfgType, klass: KfgClass, value: Descriptor) =
            FieldDescriptor(name, type, klass, this, value)

    fun default(type: KexType, nullable: Boolean): Descriptor = descriptor(context) {
        when (type) {
            is KexBool -> const(false)
            is KexByte -> const(0)
            is KexChar -> const(0)
            is KexShort -> const(0)
            is KexInt -> const(0)
            is KexLong -> const(0L)
            is KexFloat -> const(0.0F)
            is KexDouble -> const(0.0)
            is KexClass -> if (nullable) `null` else `object`(type.kfgClass(context.types))
            is KexArray -> if (nullable) `null` else array(0, type.getKfgType(context.types))
            is KexReference -> default(type.reference, nullable)
            else -> unreachable { log.error("Could not generate default descriptor value for unknown type $type") }
        }
    }

    fun default(type: KexType): Descriptor = descriptor(context) {
        when (type) {
            is KexBool -> const(false)
            is KexByte -> const(0)
            is KexChar -> const(0)
            is KexShort -> const(0)
            is KexInt -> const(0)
            is KexLong -> const(0L)
            is KexFloat -> const(0.0F)
            is KexDouble -> const(0.0)
            is KexClass -> `null`
            is KexArray -> `null`
            is KexReference -> default(type.reference)
            else -> unreachable { log.error("Could not generate default descriptor value for unknown type $type") }
        }
    }
}

fun descriptor(context: ExecutionContext, body: DescriptorBuilder.() -> Descriptor): Descriptor =
        DescriptorBuilder(context).body()

fun Descriptor.generateTypeInfo(ps: PredicateState = emptyState()): PredicateState = when (this) {
    is ObjectDescriptor -> {
        val descTerm = this.term
        val descType = this.type
        val instanceOfTerm = term { generate(KexBool()) }
        val builder = ps.builder()
        builder += state { instanceOfTerm equality (descTerm `is` descType) }
        builder += assume { instanceOfTerm equality true }
        var inlinedState = builder.apply()
        for ((_, field) in this.fields) {
            inlinedState = field.generateTypeInfo(inlinedState)
        }
        inlinedState
    }
    is FieldDescriptor -> {
        val descTerm = this.term
        when (val descType = this.value.type) {
            !is KexClass -> ps
            else -> {
                val builder = ps.builder()
                val instanceOfTerm = term { generate(KexBool()) }
                builder += state { instanceOfTerm equality (descTerm `is` descType) }
                builder += assume { instanceOfTerm equality true }
                builder.apply()
            }
        }
    }
    else -> ps
}

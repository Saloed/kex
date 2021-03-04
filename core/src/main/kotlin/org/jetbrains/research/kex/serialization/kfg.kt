package org.jetbrains.research.kex.serialization

import kotlinx.serialization.*
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.descriptors.*
import kotlinx.serialization.encoding.CompositeDecoder
import kotlinx.serialization.encoding.CompositeEncoder
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.SerializersModuleBuilder
import kotlinx.serialization.modules.polymorphic
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.*
import org.jetbrains.research.kfg.ir.value.Name
import org.jetbrains.research.kfg.ir.value.Slot
import org.jetbrains.research.kfg.ir.value.StringName
import org.jetbrains.research.kfg.ir.value.instruction.*
import org.jetbrains.research.kfg.type.Type
import org.jetbrains.research.kfg.type.parseDesc
import kotlin.reflect.KClass


fun getKfgSerialModule(cm: ClassManager): SerializersModule {
    ClassSerializer.cm = cm
    TypeSerializer.cm = cm
    return SerializersModule {
        include(binaryOpCodeSerializers())
        include(cmpOpcodeSerializers())
        include(callOpcodeSerializers())
        include(classSerializers())
        include(instructionSerializers())
        include(nameSerializers())

        contextual(Location::class, LocationSerializer)
        contextual(Type::class, TypeSerializer)
        contextual(Method::class, MethodSerializer)
    }
}

private fun binaryOpCodeSerializers() = SerializersModule {
    contextual(BinaryOpcode::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Add::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Sub::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Mul::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Div::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Rem::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Shl::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Shr::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Ushr::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.And::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Or::class, BinaryOpcodeSerializer)
    unsafeContextual(BinaryOpcode.Xor::class, BinaryOpcodeSerializer)
}

private fun cmpOpcodeSerializers() = SerializersModule {
    contextual(CmpOpcode::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Eq::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Neq::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Lt::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Gt::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Le::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Ge::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Cmp::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Cmpg::class, CmpOpcodeSerializer)
    unsafeContextual(CmpOpcode.Cmpl::class, CmpOpcodeSerializer)
}

private fun callOpcodeSerializers() = SerializersModule {
    contextual(CallOpcode::class, CallOpcodeSerializer)
    unsafeContextual(CallOpcode.Interface::class, CallOpcodeSerializer)
    unsafeContextual(CallOpcode.Virtual::class, CallOpcodeSerializer)
    unsafeContextual(CallOpcode.Static::class, CallOpcodeSerializer)
    unsafeContextual(CallOpcode.Special::class, CallOpcodeSerializer)
}

private fun classSerializers() = SerializersModule {
    contextual(Class::class, ClassSerializer)
    unsafeContextual(ConcreteClass::class, ClassSerializer)
    unsafeContextual(OuterClass::class, ClassSerializer)
}

private fun instructionSerializers() = SerializersModule {
    polymorphic(Instruction::class) {
        subclass(CallInst::class, CallInstSerializer.apply { reset() })
        subclass(NewInst::class, NewInstSerializer.apply { reset() })
        subclass(NewArrayInst::class, NewArrayInstSerializer.apply { reset() })
    }
}

private fun nameSerializers() = SerializersModule {
    polymorphic(Name::class) {
        subclass(StringName::class, StringNameSerializer.apply { reset() })
        subclass(Slot::class, SlotSerializer.apply { reset() })
    }
}

@Suppress("UNCHECKED_CAST")
private inline fun <reified Base : Any, reified T : Base> SerializersModuleBuilder.unsafeContextual(kClass: KClass<T>, serializer: KSerializer<Base>) =
        contextual(kClass, serializer as KSerializer<T>)

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = BinaryOpcode::class)
object BinaryOpcodeSerializer : KSerializer<BinaryOpcode> {
    override val descriptor: SerialDescriptor
        get() = PrimitiveSerialDescriptor("opcode", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: BinaryOpcode) {
        encoder.encodeString(value.name)
    }

    override fun deserialize(decoder: Decoder): BinaryOpcode {
        val opcode = decoder.decodeString()
        return BinaryOpcode.parse(opcode)
    }
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = CmpOpcode::class)
object CmpOpcodeSerializer : KSerializer<CmpOpcode> {
    override val descriptor: SerialDescriptor
        get() = PrimitiveSerialDescriptor("opcode", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: CmpOpcode) {
        encoder.encodeString(value.name)
    }

    override fun deserialize(decoder: Decoder): CmpOpcode {
        val opcode = decoder.decodeString()
        return CmpOpcode.parse(opcode)
    }
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = CallOpcode::class)
object CallOpcodeSerializer : KSerializer<CallOpcode> {
    override val descriptor: SerialDescriptor
        get() = PrimitiveSerialDescriptor("opcode", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: CallOpcode) {
        encoder.encodeString(value.name)
    }

    override fun deserialize(decoder: Decoder): CallOpcode {
        val opcode = decoder.decodeString()
        return CallOpcode.parse(opcode)
    }
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = Location::class)
object LocationSerializer : KSerializer<Location> {
    override val descriptor: SerialDescriptor
        get() = buildClassSerialDescriptor("Location") {
            element<String>("package")
            element<String>("file")
            element<Int>("line")
        }

    override fun serialize(encoder: Encoder, value: Location) {
        val output = encoder.beginStructure(descriptor)
        output.encodeStringElement(descriptor, 0, value.`package`.toString())
        output.encodeStringElement(descriptor, 1, value.file)
        output.encodeIntElement(descriptor, 2, value.line)
        output.endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): Location {
        val input = decoder.beginStructure(descriptor)
        lateinit var `package`: Package
        lateinit var file: String
        var line = 0
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.DECODE_DONE -> break@loop
                0 -> `package` = Package(input.decodeStringElement(descriptor, i))
                1 -> file = input.decodeStringElement(descriptor, i)
                2 -> line = input.decodeIntElement(descriptor, i)
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return Location(`package`, file, line)
    }
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = Class::class)
internal object ClassSerializer : KSerializer<Class> {
    lateinit var cm: ClassManager

    override val descriptor: SerialDescriptor
        get() = PrimitiveSerialDescriptor("fullname", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: Class) {
        encoder.encodeString(value.fullname)
    }

    override fun deserialize(decoder: Decoder) = cm[decoder.decodeString()]
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = Method::class)
internal object MethodSerializer : KSerializer<Method> {
    override val descriptor: SerialDescriptor
        get() = buildClassSerialDescriptor("Method") {
            element("class", ClassSerializer.descriptor)
            element<String>("name")
            element("retval", TypeSerializer.descriptor)
            element("arguments", ListSerializer(TypeSerializer).descriptor)
        }

    override fun serialize(encoder: Encoder, value: Method) {
        val output = encoder.beginStructure(descriptor)
        output.encodeSerializableElement(descriptor, 0, ClassSerializer, value.`class`)
        output.encodeStringElement(descriptor, 1, value.name)
        output.encodeSerializableElement(descriptor, 2, TypeSerializer, value.returnType)
        output.encodeSerializableElement(descriptor, 3, ListSerializer(TypeSerializer), value.argTypes.toList())
        output.endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): Method {
        val input = decoder.beginStructure(descriptor)
        lateinit var klass: Class
        lateinit var name: String
        lateinit var retval: Type
        lateinit var argTypes: Array<Type>
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.DECODE_DONE -> break@loop
                0 -> klass = input.decodeSerializableElement(descriptor, i, ClassSerializer)
                1 -> name = input.decodeStringElement(descriptor, i)
                2 -> retval = input.decodeSerializableElement(descriptor, i, TypeSerializer)
                3 -> argTypes = input.decodeSerializableElement(descriptor, i, ListSerializer(TypeSerializer)).toTypedArray()
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return klass.getMethod(name, MethodDesc(argTypes, retval))
    }
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = Type::class)
internal object TypeSerializer : KSerializer<Type> {
    lateinit var cm: ClassManager

    override val descriptor: SerialDescriptor
        get() = buildClassSerialDescriptor("Type") {
            element<String>("type")
        }

    override fun serialize(encoder: Encoder, value: Type) {
        val output = encoder.beginStructure(descriptor)
        output.encodeStringElement(descriptor, 0, value.asmDesc)
        output.endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): Type {
        val input = decoder.beginStructure(descriptor)
        lateinit var type: Type
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.DECODE_DONE -> break@loop
                0 -> type = parseDesc(cm.type, input.decodeStringElement(descriptor, i))
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return type
    }
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = CallInst::class)
internal object CallInstSerializer : KSerializer<CallInst> {
    private val referenceSerializer = object : ReferenceSerializer<CallInst>(CallInst::class) {
        override fun ClassSerialDescriptorBuilder.buildDescriptor() {
            element("method", MethodSerializer.descriptor)
            element("opcode", CallOpcodeSerializer.descriptor)
            element("class", ClassSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
            element<Int>("id")
        }

        override fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: CallInst) {
            encodeSerializableElement(descriptor, 0, MethodSerializer, value.method)
            encodeSerializableElement(descriptor, 1, CallOpcodeSerializer, value.opcode)
            encodeSerializableElement(descriptor, 2, ClassSerializer, value.`class`)
            encodeSerializableElement(descriptor, 3, LocationSerializer, value.location)
            encodeIntElement(descriptor, 4, value.id)
        }

        override fun Decoder.deserializeObject(): ReferencedObject<CallInst> {
            lateinit var method: Method
            lateinit var opcode: CallOpcode
            lateinit var klass: Class
            lateinit var location: Location
            var id: Int = -1
            val ref = deserializeObjectAndReference { descriptor, i ->
                when (i) {
                    0 -> method = decodeSerializableElement(descriptor, i, MethodSerializer)
                    1 -> opcode = decodeSerializableElement(descriptor, i, CallOpcodeSerializer)
                    2 -> klass = decodeSerializableElement(descriptor, i, ClassSerializer)
                    3 -> location = decodeSerializableElement(descriptor, i, LocationSerializer)
                    4 -> id = decodeIntElement(descriptor, i)
                    else -> throw SerializationException("Unknown index $i")
                }
            }
            val obj = CallInst(id, opcode, method, klass, emptyArray()).update(loc = location) as CallInst
            return ReferencedObject(ref, obj)
        }
    }
    override val descriptor: SerialDescriptor
        get() = referenceSerializer.descriptor

    override fun serialize(encoder: Encoder, value: CallInst) = referenceSerializer.serialize(encoder, value)
    override fun deserialize(decoder: Decoder): CallInst = referenceSerializer.deserialize(decoder)
    fun reset() = referenceSerializer.reset()
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = NewInst::class)
internal object NewInstSerializer : KSerializer<NewInst> {
    private val referenceSerializer = object : ReferenceSerializer<NewInst>(NewInst::class) {
        override fun ClassSerialDescriptorBuilder.buildDescriptor() {
            element("name", PolymorphicSerializer(Name::class).descriptor)
            element("type", TypeSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
            element<Int>("id")
        }

        override fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: NewInst) {
            encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Name::class), value.name)
            encodeSerializableElement(descriptor, 1, TypeSerializer, value.type)
            encodeSerializableElement(descriptor, 2, LocationSerializer, value.location)
            encodeIntElement(descriptor, 3, value.id)
        }

        override fun Decoder.deserializeObject(): ReferencedObject<NewInst> {
            lateinit var name: Name
            lateinit var type: Type
            lateinit var location: Location
            var id: Int = -1
            val ref = deserializeObjectAndReference { descriptor, i ->
                when (i) {
                    0 -> name = decodeSerializableElement(descriptor, i, PolymorphicSerializer(Name::class))
                    1 -> type = decodeSerializableElement(descriptor, i, TypeSerializer)
                    2 -> location = decodeSerializableElement(descriptor, i, LocationSerializer)
                    3 -> id = decodeIntElement(descriptor, i)
                    else -> throw SerializationException("Unknown index $i")
                }
            }
            val obj = NewInst(id, name, type).update(loc = location) as NewInst
            return ReferencedObject(ref, obj)
        }
    }
    override val descriptor: SerialDescriptor
        get() = referenceSerializer.descriptor

    override fun serialize(encoder: Encoder, value: NewInst) = referenceSerializer.serialize(encoder, value)
    override fun deserialize(decoder: Decoder): NewInst = referenceSerializer.deserialize(decoder)
    fun reset() = referenceSerializer.reset()
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = NewArrayInst::class)
internal object NewArrayInstSerializer : KSerializer<NewArrayInst> {
    private val referenceSerializer = object : ReferenceSerializer<NewArrayInst>(NewArrayInst::class) {
        override fun ClassSerialDescriptorBuilder.buildDescriptor() {
            element("name", PolymorphicSerializer(Name::class).descriptor)
            element("type", TypeSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
            element<Int>("id")
        }

        override fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: NewArrayInst) {
            encodeSerializableElement(descriptor, 0, PolymorphicSerializer(Name::class), value.name)
            encodeSerializableElement(descriptor, 1, TypeSerializer, value.type)
            encodeSerializableElement(descriptor, 2, LocationSerializer, value.location)
            encodeIntElement(descriptor, 3, value.id)
        }

        override fun Decoder.deserializeObject(): ReferencedObject<NewArrayInst> {
            lateinit var name: Name
            lateinit var type: Type
            lateinit var location: Location
            var id: Int = -1
            val ref = deserializeObjectAndReference { descriptor, i ->
                when (i) {
                    0 -> name = decodeSerializableElement(descriptor, i, PolymorphicSerializer(Name::class))
                    1 -> type = decodeSerializableElement(descriptor, i, TypeSerializer)
                    2 -> location = decodeSerializableElement(descriptor, i, LocationSerializer)
                    3 -> id = decodeIntElement(descriptor, i)
                    else -> throw SerializationException("Unknown index $i")
                }
            }
            val obj = NewArrayInst(id, name, type, emptyArray()).update(loc = location) as NewArrayInst
            return ReferencedObject(ref, obj)
        }
    }
    override val descriptor: SerialDescriptor
        get() = referenceSerializer.descriptor

    override fun serialize(encoder: Encoder, value: NewArrayInst) = referenceSerializer.serialize(encoder, value)
    override fun deserialize(decoder: Decoder): NewArrayInst = referenceSerializer.deserialize(decoder)
    fun reset() = referenceSerializer.reset()
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = StringName::class)
internal object StringNameSerializer : KSerializer<StringName> {
    private val referenceSerializer = object : ReferenceSerializer<StringName>(StringName::class) {
        override fun ClassSerialDescriptorBuilder.buildDescriptor() {
            element<String>("name")
        }

        override fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: StringName) {
            encodeStringElement(descriptor, 0, value.name)
        }

        override fun Decoder.deserializeObject(): ReferencedObject<StringName> {
            lateinit var name: String
            val ref = deserializeObjectAndReference { descriptor, i ->
                when (i) {
                    0 -> name = decodeStringElement(descriptor, i)
                    else -> throw SerializationException("Unknown index $i")
                }
            }
            return ReferencedObject(ref, StringName(name))
        }
    }
    override val descriptor: SerialDescriptor
        get() = referenceSerializer.descriptor

    override fun serialize(encoder: Encoder, value: StringName) = referenceSerializer.serialize(encoder, value)
    override fun deserialize(decoder: Decoder): StringName = referenceSerializer.deserialize(decoder)
    fun reset() = referenceSerializer.reset()
}

@OptIn(ExperimentalSerializationApi::class)
@Serializer(forClass = Slot::class)
internal object SlotSerializer : KSerializer<Slot> {
    private val referenceSerializer = object : ReferenceSerializer<Slot>(Slot::class) {
        override fun ClassSerialDescriptorBuilder.buildDescriptor() {}
        override fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: Slot) {}
        override fun Decoder.deserializeObject(): ReferencedObject<Slot> {
            val ref = deserializeObjectAndReference { _, i -> throw SerializationException("Unknown index $i") }
            return ReferencedObject(ref, Slot())
        }
    }
    override val descriptor: SerialDescriptor
        get() = referenceSerializer.descriptor

    override fun serialize(encoder: Encoder, value: Slot) = referenceSerializer.serialize(encoder, value)
    override fun deserialize(decoder: Decoder): Slot = referenceSerializer.deserialize(decoder)
    fun reset() = referenceSerializer.reset()
}

internal data class ReferencedObject<T : Any>(val ref: String, val obj: T)

internal abstract class ReferenceSerializer<T : Any>(val type: KClass<T>) {
    private val referenceCache = hashMapOf<String, T>()
    abstract fun ClassSerialDescriptorBuilder.buildDescriptor()

    @OptIn(ExperimentalSerializationApi::class)
    private val refIndex: Int
        get() = descriptor.elementsCount - 1

    val descriptor: SerialDescriptor
        get() = buildClassSerialDescriptor("Reference[${type.qualifiedName}]") {
            buildDescriptor()
            element<String>("ref")
        }

    abstract fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: T)

    fun serialize(encoder: Encoder, value: T) {
        val output = encoder.beginStructure(descriptor)
        output.serializeElements(descriptor, value)
        output.encodeStringElement(descriptor, refIndex, objectId(value))
        output.endStructure(descriptor)
    }

    fun deserialize(decoder: Decoder): T {
        val refObj = decoder.deserializeObject()
        return referenceCache.getOrPut(refObj.ref) { refObj.obj }
    }

    abstract fun Decoder.deserializeObject(): ReferencedObject<T>

    fun Decoder.deserializeObjectAndReference(builder: CompositeDecoder.(SerialDescriptor, Int) -> Unit): String {
        val input = beginStructure(descriptor)
        lateinit var objId: String
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.DECODE_DONE -> break@loop
                refIndex -> objId = input.decodeStringElement(descriptor, i)
                else -> input.builder(descriptor, i)
            }
        }
//        input.endStructure(descriptor) // fixme: polymorphic field key missed
        return objId
    }

    fun reset(): Unit = referenceCache.clear()

    private fun objectId(obj: Any) = Integer.toHexString(System.identityHashCode(obj))
}

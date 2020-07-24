package org.jetbrains.research.kex.serialization

import kotlinx.serialization.*
import kotlinx.serialization.builtins.list
import kotlinx.serialization.modules.SerialModule
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.plus
import kotlinx.serialization.modules.serializersModuleOf
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.*
import org.jetbrains.research.kfg.ir.value.Name
import org.jetbrains.research.kfg.ir.value.Slot
import org.jetbrains.research.kfg.ir.value.StringName
import org.jetbrains.research.kfg.ir.value.instruction.*
import org.jetbrains.research.kfg.type.Type
import org.jetbrains.research.kfg.type.parseDesc


fun getKfgSerialModule(cm: ClassManager): SerialModule {
    ClassSerializer.cm = cm
    TypeSerializer.cm = cm
    return serializersModuleOf(mapOf(
            //BinaryOpcodes
            BinaryOpcode::class to BinaryOpcodeSerializer,
            BinaryOpcode.Add::class to BinaryOpcodeSerializer,
            BinaryOpcode.Sub::class to BinaryOpcodeSerializer,
            BinaryOpcode.Mul::class to BinaryOpcodeSerializer,
            BinaryOpcode.Div::class to BinaryOpcodeSerializer,
            BinaryOpcode.Rem::class to BinaryOpcodeSerializer,
            BinaryOpcode.Shl::class to BinaryOpcodeSerializer,
            BinaryOpcode.Shr::class to BinaryOpcodeSerializer,
            BinaryOpcode.Ushr::class to BinaryOpcodeSerializer,
            BinaryOpcode.And::class to BinaryOpcodeSerializer,
            BinaryOpcode.Or::class to BinaryOpcodeSerializer,
            BinaryOpcode.Xor::class to BinaryOpcodeSerializer,
            //CmpOpcodes
            CmpOpcode::class to CmpOpcodeSerializer,
            CmpOpcode.Eq::class to CmpOpcodeSerializer,
            CmpOpcode.Neq::class to CmpOpcodeSerializer,
            CmpOpcode.Lt::class to CmpOpcodeSerializer,
            CmpOpcode.Gt::class to CmpOpcodeSerializer,
            CmpOpcode.Le::class to CmpOpcodeSerializer,
            CmpOpcode.Ge::class to CmpOpcodeSerializer,
            CmpOpcode.Cmp::class to CmpOpcodeSerializer,
            CmpOpcode.Cmpg::class to CmpOpcodeSerializer,
            CmpOpcode.Cmpl::class to CmpOpcodeSerializer,
            //CallOpcodes
            CallOpcode::class to CallOpcodeSerializer,
            CallOpcode.Interface::class to CallOpcodeSerializer,
            CallOpcode.Virtual::class to CallOpcodeSerializer,
            CallOpcode.Static::class to CallOpcodeSerializer,
            CallOpcode.Special::class to CallOpcodeSerializer,
            //Classes
            Class::class to ClassSerializer,
            ConcreteClass::class to ClassSerializer,
            OuterClass::class to ClassSerializer,
            // other classes
            Location::class to LocationSerializer,
            Type::class to TypeSerializer,
            Method::class to MethodSerializer
    )) + SerializersModule {
        polymorphic(InstructionSerializer) {
            CallInst::class with CallInstSerializer.apply { reset() }
            NewInst::class with NewInstSerializer.apply { reset() }
            NewArrayInst::class with NewArrayInstSerializer.apply { reset() }
        }
        polymorphic(NameSerializer) {
            StringName::class with StringNameSerializer.apply { reset() }
            Slot::class with SlotSerializer.apply { reset() }
        }
    }
}

@Serializer(forClass = BinaryOpcode::class)
object BinaryOpcodeSerializer : KSerializer<BinaryOpcode> {
    override val descriptor: SerialDescriptor
        get() = PrimitiveDescriptor("opcode", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: BinaryOpcode) {
        encoder.encodeString(value.name)
    }

    override fun deserialize(decoder: Decoder): BinaryOpcode {
        val opcode = decoder.decodeString()
        return BinaryOpcode.parse(opcode)
    }
}

@Serializer(forClass = CmpOpcode::class)
object CmpOpcodeSerializer : KSerializer<CmpOpcode> {
    override val descriptor: SerialDescriptor
        get() = PrimitiveDescriptor("opcode", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: CmpOpcode) {
        encoder.encodeString(value.name)
    }

    override fun deserialize(decoder: Decoder): CmpOpcode {
        val opcode = decoder.decodeString()
        return CmpOpcode.parse(opcode)
    }
}

@Serializer(forClass = CallOpcode::class)
object CallOpcodeSerializer : KSerializer<CallOpcode> {
    override val descriptor: SerialDescriptor
        get() = PrimitiveDescriptor("opcode", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: CallOpcode) {
        encoder.encodeString(value.name)
    }

    override fun deserialize(decoder: Decoder): CallOpcode {
        val opcode = decoder.decodeString()
        return CallOpcode.parse(opcode)
    }
}

@Serializer(forClass = Location::class)
object LocationSerializer : KSerializer<Location> {
    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("Location") {
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
                CompositeDecoder.READ_DONE -> break@loop
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

@Serializer(forClass = Class::class)
internal object ClassSerializer : KSerializer<Class> {
    lateinit var cm: ClassManager

    override val descriptor: SerialDescriptor
        get() = PrimitiveDescriptor("fullname", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: Class) {
        encoder.encodeString(value.fullname)
    }

    override fun deserialize(decoder: Decoder) = cm[decoder.decodeString()]
}

@Serializer(forClass = Method::class)
internal object MethodSerializer : KSerializer<Method> {
    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("Method") {
            element("class", ClassSerializer.descriptor)
            element<String>("name")
            element("retval", TypeSerializer.descriptor)
            element("arguments", TypeSerializer.list.descriptor)
        }

    override fun serialize(encoder: Encoder, value: Method) {
        val output = encoder.beginStructure(descriptor)
        output.encodeSerializableElement(descriptor, 0, ClassSerializer, value.`class`)
        output.encodeStringElement(descriptor, 1, value.name)
        output.encodeSerializableElement(descriptor, 2, TypeSerializer, value.returnType)
        output.encodeSerializableElement(descriptor, 3, TypeSerializer.list, value.argTypes.toList())
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
                CompositeDecoder.READ_DONE -> break@loop
                0 -> klass = input.decodeSerializableElement(descriptor, i, ClassSerializer)
                1 -> name = input.decodeStringElement(descriptor, i)
                2 -> retval = input.decodeSerializableElement(descriptor, i, TypeSerializer)
                3 -> argTypes = input.decodeSerializableElement(descriptor, i, TypeSerializer.list).toTypedArray()
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return klass.getMethod(name, MethodDesc(argTypes, retval))
    }
}

@Serializer(forClass = Type::class)
private object TypeSerializer : KSerializer<Type> {
    lateinit var cm: ClassManager

    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("Type") {
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
                CompositeDecoder.READ_DONE -> break@loop
                0 -> type = parseDesc(cm.type, input.decodeStringElement(descriptor, i))
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return type
    }
}

class ReferenceSerializer<T : Any>(val serializer: KSerializer<T>) : KSerializer<T> {
    private val deserializationCache = hashMapOf<String, T>()

    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("Reference[${serializer.descriptor.serialName}]") {
            element<String>("ref")
            element("object", serializer.descriptor)
        }

    override fun serialize(encoder: Encoder, value: T) {
        val output = encoder.beginStructure(descriptor)
        output.encodeStringElement(descriptor, 0, objectId(value))
        output.encodeSerializableElement(descriptor, 1, serializer, value)
        output.endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): T {
        val input = decoder.beginStructure(descriptor)
        lateinit var objId: String
        lateinit var obj: T
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.READ_DONE -> break@loop
                0 -> objId = input.decodeStringElement(descriptor, i)
                1 -> obj = input.decodeSerializableElement(descriptor, i, serializer)
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return deserializationCache.getOrPut(objId) { obj }
    }

    fun reset(): Unit = deserializationCache.clear()

    private fun objectId(obj: Any) = Integer.toHexString(System.identityHashCode(obj))
}

private inline fun <reified T : Any> KSerializer<T>.withReference() = ReferenceSerializer<T>(this)

private val InstructionSerializer = PolymorphicSerializer(Instruction::class)
private val CallInstSerializer = CallInstSerializerBase.withReference()
private val NewInstSerializer = NewInstSerializerBase.withReference()
private val NewArrayInstSerializer = NewArrayInstSerializerBase.withReference()

@Serializer(forClass = CallInst::class)
private object CallInstSerializerBase : KSerializer<CallInst> {
    lateinit var cm: ClassManager

    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("CallInst") {
            element("method", MethodSerializer.descriptor)
            element("opcode", CallOpcodeSerializer.descriptor)
            element("class", ClassSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
        }

    override fun serialize(encoder: Encoder, value: CallInst) {
        val output = encoder.beginStructure(descriptor)
        output.encodeSerializableElement(descriptor, 0, MethodSerializer, value.method)
        output.encodeSerializableElement(descriptor, 1, CallOpcodeSerializer, value.opcode)
        output.encodeSerializableElement(descriptor, 2, ClassSerializer, value.`class`)
        output.encodeSerializableElement(descriptor, 3, LocationSerializer, value.location)
        output.endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): CallInst {
        val input = decoder.beginStructure(descriptor)
        lateinit var method: Method
        lateinit var opcode: CallOpcode
        lateinit var klass: Class
        lateinit var location: Location
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.READ_DONE -> break@loop
                0 -> method = input.decodeSerializableElement(descriptor, i, MethodSerializer)
                1 -> opcode = input.decodeSerializableElement(descriptor, i, CallOpcodeSerializer)
                2 -> klass = input.decodeSerializableElement(descriptor, i, ClassSerializer)
                3 -> location = input.decodeSerializableElement(descriptor, i, LocationSerializer)
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return CallInst(opcode, method, klass, emptyArray()).update(loc = location) as CallInst
    }
}

@Serializer(forClass = NewInst::class)
private object NewInstSerializerBase : KSerializer<NewInst> {
    lateinit var cm: ClassManager

    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("NewInst") {
            element("name", NameSerializer.descriptor)
            element("type", TypeSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
        }

    override fun serialize(encoder: Encoder, value: NewInst) {
        val output = encoder.beginStructure(descriptor)
        output.encodeSerializableElement(descriptor, 0, NameSerializer, value.name)
        output.encodeSerializableElement(descriptor, 1, TypeSerializer, value.type)
        output.encodeSerializableElement(descriptor, 2, LocationSerializer, value.location)
        output.endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): NewInst {
        val input = decoder.beginStructure(descriptor)
        lateinit var name: Name
        lateinit var type: Type
        lateinit var location: Location
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.READ_DONE -> break@loop
                0 -> name = input.decodeSerializableElement(descriptor, i, NameSerializer)
                1 -> type = input.decodeSerializableElement(descriptor, i, TypeSerializer)
                2 -> location = input.decodeSerializableElement(descriptor, i, LocationSerializer)
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return NewInst(name, type).update(loc = location) as NewInst
    }
}

@Serializer(forClass = NewArrayInst::class)
private object NewArrayInstSerializerBase : KSerializer<NewArrayInst> {
    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("NewArrayInst") {
            element("name", NameSerializer.descriptor)
            element("type", TypeSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
        }

    override fun serialize(encoder: Encoder, value: NewArrayInst) {
        val output = encoder.beginStructure(descriptor)
        output.encodeSerializableElement(descriptor, 0, NameSerializer, value.name)
        output.encodeSerializableElement(descriptor, 1, TypeSerializer, value.type)
        output.encodeSerializableElement(descriptor, 2, LocationSerializer, value.location)
        output.endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): NewArrayInst {
        val input = decoder.beginStructure(descriptor)
        lateinit var name: Name
        lateinit var type: Type
        lateinit var location: Location
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.READ_DONE -> break@loop
                0 -> name = input.decodeSerializableElement(descriptor, i, NameSerializer)
                1 -> type = input.decodeSerializableElement(descriptor, i, TypeSerializer)
                2 -> location = input.decodeSerializableElement(descriptor, i, LocationSerializer)
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return NewArrayInst(name, type, emptyArray()).update(loc = location) as NewArrayInst
    }
}

private val NameSerializer = PolymorphicSerializer(Name::class)
private val StringNameSerializer = StringNameSerializerBase.withReference()
private val SlotSerializer = SlotSerializerBase.withReference()

@Serializer(forClass = StringName::class)
private object StringNameSerializerBase : KSerializer<StringName> {
    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("StringName") {
            element<String>("name")
        }

    override fun serialize(encoder: Encoder, value: StringName) {
        val output = encoder.beginStructure(descriptor)
        output.encodeStringElement(descriptor, 0, value.name)
        output.endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): StringName {
        val input = decoder.beginStructure(descriptor)
        lateinit var name: String
        loop@ while (true) {
            when (val i = input.decodeElementIndex(descriptor)) {
                CompositeDecoder.READ_DONE -> break@loop
                0 -> name = input.decodeStringElement(descriptor, i)
                else -> throw SerializationException("Unknown index $i")
            }
        }
        input.endStructure(descriptor)
        return StringName(name)
    }
}

@Serializer(forClass = Slot::class)
private object SlotSerializerBase : KSerializer<Slot> {
    override val descriptor: SerialDescriptor
        get() = SerialDescriptor("Slot") {}

    override fun serialize(encoder: Encoder, value: Slot) {
        encoder.beginStructure(descriptor).endStructure(descriptor)
    }

    override fun deserialize(decoder: Decoder): Slot {
        decoder.beginStructure(descriptor).endStructure(descriptor)
        return Slot()
    }
}


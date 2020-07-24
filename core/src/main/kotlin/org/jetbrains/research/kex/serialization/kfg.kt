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
import kotlin.reflect.KClass


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
            subclass(CallInstSerializer.apply { reset() })
            subclass(NewInstSerializer.apply { reset() })
            subclass(NewArrayInstSerializer.apply { reset() })
        }
        polymorphic(NameSerializer) {
            subclass(StringNameSerializer.apply { reset() })
            subclass(SlotSerializer.apply { reset() })
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
internal object TypeSerializer : KSerializer<Type> {
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

internal val InstructionSerializer = PolymorphicSerializer(Instruction::class)

@Serializer(forClass = CallInst::class)
internal object CallInstSerializer : KSerializer<CallInst> {
    private val referenceSerializer = object : ReferenceSerializer<CallInst>(CallInst::class) {
        override fun SerialDescriptorBuilder.buildDescriptor() {
            element("method", MethodSerializer.descriptor)
            element("opcode", CallOpcodeSerializer.descriptor)
            element("class", ClassSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
        }

        override fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: CallInst) {
            encodeSerializableElement(descriptor, 0, MethodSerializer, value.method)
            encodeSerializableElement(descriptor, 1, CallOpcodeSerializer, value.opcode)
            encodeSerializableElement(descriptor, 2, ClassSerializer, value.`class`)
            encodeSerializableElement(descriptor, 3, LocationSerializer, value.location)
        }

        override fun Decoder.deserializeObject(): ReferencedObject<CallInst> {
            lateinit var method: Method
            lateinit var opcode: CallOpcode
            lateinit var klass: Class
            lateinit var location: Location
            val ref = deserializeObjectAndReference { descriptor, i ->
                when (i) {
                    0 -> method = decodeSerializableElement(descriptor, i, MethodSerializer)
                    1 -> opcode = decodeSerializableElement(descriptor, i, CallOpcodeSerializer)
                    2 -> klass = decodeSerializableElement(descriptor, i, ClassSerializer)
                    3 -> location = decodeSerializableElement(descriptor, i, LocationSerializer)
                    else -> throw SerializationException("Unknown index $i")
                }
            }
            val obj = CallInst(opcode, method, klass, emptyArray()).update(loc = location) as CallInst
            return ReferencedObject(ref, obj)
        }
    }
    override val descriptor: SerialDescriptor
        get() = referenceSerializer.descriptor

    override fun serialize(encoder: Encoder, value: CallInst) = referenceSerializer.serialize(encoder, value)
    override fun deserialize(decoder: Decoder): CallInst = referenceSerializer.deserialize(decoder)
    fun reset() = referenceSerializer.reset()
}

@Serializer(forClass = NewInst::class)
internal object NewInstSerializer : KSerializer<NewInst> {
    private val referenceSerializer = object : ReferenceSerializer<NewInst>(NewInst::class) {
        override fun SerialDescriptorBuilder.buildDescriptor() {
            element("name", NameSerializer.descriptor)
            element("type", TypeSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
        }

        override fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: NewInst) {
            encodeSerializableElement(descriptor, 0, NameSerializer, value.name)
            encodeSerializableElement(descriptor, 1, TypeSerializer, value.type)
            encodeSerializableElement(descriptor, 2, LocationSerializer, value.location)
        }

        override fun Decoder.deserializeObject(): ReferencedObject<NewInst> {
            lateinit var name: Name
            lateinit var type: Type
            lateinit var location: Location
            val ref = deserializeObjectAndReference { descriptor, i ->
                when (i) {
                    0 -> name = decodeSerializableElement(descriptor, i, NameSerializer)
                    1 -> type = decodeSerializableElement(descriptor, i, TypeSerializer)
                    2 -> location = decodeSerializableElement(descriptor, i, LocationSerializer)
                    else -> throw SerializationException("Unknown index $i")
                }
            }
            val obj = NewInst(name, type).update(loc = location) as NewInst
            return ReferencedObject(ref, obj)
        }
    }
    override val descriptor: SerialDescriptor
        get() = referenceSerializer.descriptor

    override fun serialize(encoder: Encoder, value: NewInst) = referenceSerializer.serialize(encoder, value)
    override fun deserialize(decoder: Decoder): NewInst = referenceSerializer.deserialize(decoder)
    fun reset() = referenceSerializer.reset()
}

@Serializer(forClass = NewArrayInst::class)
internal object NewArrayInstSerializer : KSerializer<NewArrayInst> {
    private val referenceSerializer = object : ReferenceSerializer<NewArrayInst>(NewArrayInst::class) {
        override fun SerialDescriptorBuilder.buildDescriptor() {
            element("name", NameSerializer.descriptor)
            element("type", TypeSerializer.descriptor)
            element("location", LocationSerializer.descriptor)
        }

        override fun CompositeEncoder.serializeElements(descriptor: SerialDescriptor, value: NewArrayInst) {
            encodeSerializableElement(descriptor, 0, NameSerializer, value.name)
            encodeSerializableElement(descriptor, 1, TypeSerializer, value.type)
            encodeSerializableElement(descriptor, 2, LocationSerializer, value.location)
        }

        override fun Decoder.deserializeObject(): ReferencedObject<NewArrayInst> {
            lateinit var name: Name
            lateinit var type: Type
            lateinit var location: Location
            val ref = deserializeObjectAndReference { descriptor, i ->
                when (i) {
                    0 -> name = decodeSerializableElement(descriptor, i, NameSerializer)
                    1 -> type = decodeSerializableElement(descriptor, i, TypeSerializer)
                    2 -> location = decodeSerializableElement(descriptor, i, LocationSerializer)
                    else -> throw SerializationException("Unknown index $i")
                }
            }
            val obj = NewArrayInst(name, type, emptyArray()).update(loc = location) as NewArrayInst
            return ReferencedObject(ref, obj)
        }
    }
    override val descriptor: SerialDescriptor
        get() = referenceSerializer.descriptor

    override fun serialize(encoder: Encoder, value: NewArrayInst) = referenceSerializer.serialize(encoder, value)
    override fun deserialize(decoder: Decoder): NewArrayInst = referenceSerializer.deserialize(decoder)
    fun reset() = referenceSerializer.reset()
}

internal val NameSerializer = PolymorphicSerializer(Name::class)

@Serializer(forClass = StringName::class)
internal object StringNameSerializer : KSerializer<StringName> {
    private val referenceSerializer = object : ReferenceSerializer<StringName>(StringName::class) {
        override fun SerialDescriptorBuilder.buildDescriptor() {
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

@Serializer(forClass = Slot::class)
internal object SlotSerializer : KSerializer<Slot> {
    private val referenceSerializer = object : ReferenceSerializer<Slot>(Slot::class) {
        override fun SerialDescriptorBuilder.buildDescriptor() {}
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
    abstract fun SerialDescriptorBuilder.buildDescriptor()

    private val refIndex: Int
        get() = descriptor.elementsCount - 1

    val descriptor: SerialDescriptor
        get() = SerialDescriptor("Reference[${type.qualifiedName}]") {
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
                CompositeDecoder.READ_DONE -> break@loop
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

package org.jetbrains.research.kex.serialization

import kotlinx.serialization.UnsafeSerializationApi
import kotlinx.serialization.json.Json
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.serializer
import org.jetbrains.research.kfg.ClassManager

abstract class AbstractSerializer(val context: SerializersModule) {
    val json = Json {
        encodeDefaults = false
        ignoreUnknownKeys = false
        prettyPrint = true
        useArrayPolymorphism = false
        classDiscriminator = "className"
        serializersModule = context
    }

    @OptIn(UnsafeSerializationApi::class)
    inline fun <reified T : Any> toJson(t: T) = json.encodeToString(T::class.serializer(), t)

    @OptIn(UnsafeSerializationApi::class)
    inline fun <reified T : Any> fromJson(str: String) = json.decodeFromString(T::class.serializer(), str)
}

class KexSerializer(val cm: ClassManager) : AbstractSerializer(getPredicateStateSerialModule(cm))

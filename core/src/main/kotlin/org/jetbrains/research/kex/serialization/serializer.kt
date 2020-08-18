package org.jetbrains.research.kex.serialization

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


    inline fun <reified T : Any> toJson(t: T) = json.encodeToString(serializer<T>(), t)


    inline fun <reified T : Any> fromJson(str: String) = json.decodeFromString(serializer<T>(), str)
}

class KexSerializer(val cm: ClassManager) : AbstractSerializer(getPredicateStateSerialModule(cm))

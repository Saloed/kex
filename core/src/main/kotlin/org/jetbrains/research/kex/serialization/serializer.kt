package org.jetbrains.research.kex.serialization

import kotlinx.serialization.UnsafeSerializationApi
import kotlinx.serialization.UnstableDefault
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonConfiguration
import kotlinx.serialization.modules.SerialModule
import kotlinx.serialization.serializer
import org.jetbrains.research.kfg.ClassManager

abstract class AbstractSerializer(val context: SerialModule) {
    @OptIn(UnstableDefault::class)
    protected val configuration = JsonConfiguration(
            encodeDefaults = false,
            ignoreUnknownKeys = false,
            unquotedPrint = false,
            prettyPrint = true,
            useArrayPolymorphism = false,
            classDiscriminator = "className"
    )
    val json = Json(configuration, context)

    @OptIn(UnsafeSerializationApi::class)
    inline fun <reified T: Any> toJson(t: T) = json.stringify(T::class.serializer(), t)
    @OptIn(UnsafeSerializationApi::class)
    inline fun <reified T: Any> fromJson(str: String) = json.parse(T::class.serializer(), str)
}

class KexSerializer(val cm: ClassManager) : AbstractSerializer(getPredicateStateSerialModule(cm))

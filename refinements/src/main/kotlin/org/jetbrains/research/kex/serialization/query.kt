package org.jetbrains.research.kex.serialization

import kotlinx.serialization.InternalSerializationApi
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.polymorphic
import kotlinx.serialization.serializer
import org.jetbrains.research.kex.refinements.solver.CallResolveSolverQuery
import org.jetbrains.research.kex.refinements.solver.CallResolveSolverQueryWrapper
import org.jetbrains.research.kex.refinements.solver.RefinementsSolverQuery
import org.jetbrains.research.kex.refinements.solver.SolverQuery
import org.jetbrains.research.kfg.ClassManager
import kotlin.reflect.KClass

fun getQuerySerialModule(cm: ClassManager) = SerializersModule {
    include(getPredicateStateSerialModule(cm))
    polymorphic(SolverQuery::class) {
        subclass(RefinementsSolverQuery::class, serializer())
        subclass(CallResolveSolverQuery::class, serializer())
        subclass(CallResolveSolverQueryWrapper::class, serializer())
    }
}

class RefinementsKexSerializer(val cm: ClassManager): AbstractSerializer(getQuerySerialModule(cm)){
    @OptIn(InternalSerializationApi::class)
    fun <T : Any> fromJson(str: String, cls: KClass<T>) = json.decodeFromString(cls.serializer(), str)
    @OptIn(InternalSerializationApi::class)
    fun <T : Any> toJson(value: T, cls: KClass<T>) = json.encodeToString(cls.serializer(), value)
}

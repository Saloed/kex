package org.jetbrains.research.kex.serialization

import kotlinx.serialization.InternalSerializationApi
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.polymorphic
import kotlinx.serialization.serializer
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.*
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kfg.ClassManager
import kotlin.reflect.KClass


@OptIn(InternalSerializationApi::class)
val kexTypeSerialModule: SerializersModule
    get() = SerializersModule {
        polymorphic(KexType::class) {
            KexType.types.forEach { (_, klass) ->
                subclass(klass, klass.serializer())
            }
        }
    }

@OptIn(InternalSerializationApi::class)
fun getTermSerialModule(cm: ClassManager): SerializersModule = SerializersModule {
    include(getKfgSerialModule(cm))
    include(kexTypeSerialModule)
    polymorphic(Term::class) {
        Term.terms.forEach { (_, klass) ->
            @Suppress("UNCHECKED_CAST") val any = klass.kotlin as KClass<Term>
            subclass(any, any.serializer())
        }
    }

}

val predicateTypeSerialModule: SerializersModule
    get() = SerializersModule {
        polymorphic(PredicateType::class) {
            subclass(PredicateType.Path::class, PredicateType.Path.serializer())
            subclass(PredicateType.State::class, PredicateType.State.serializer())
            subclass(PredicateType.Assume::class, PredicateType.Assume.serializer())
            subclass(PredicateType.Require::class, PredicateType.Require.serializer())
        }
    }

@OptIn(InternalSerializationApi::class)
fun getPredicateSerialModule(cm: ClassManager): SerializersModule = SerializersModule {
    include(getTermSerialModule(cm))
    include(predicateTypeSerialModule)
    include(getNewObjectIdentifierSerialModule())
    polymorphic(Predicate::class) {
        Predicate.predicates.forEach { (_, klass) ->
            @Suppress("UNCHECKED_CAST") val any = klass.kotlin as KClass<Predicate>
            subclass(any, any.serializer())
        }
    }
}

@OptIn(InternalSerializationApi::class)
fun getPredicateStateSerialModule(cm: ClassManager): SerializersModule = SerializersModule {
    include(getPredicateSerialModule(cm))
    polymorphic(PredicateState::class) {
        PredicateState.states.forEach { (_, klass) ->
            @Suppress("UNCHECKED_CAST") val any = klass.kotlin as KClass<PredicateState>
            subclass(any, any.serializer())
        }
    }
}

fun getNewObjectIdentifierSerialModule() = SerializersModule {
    polymorphic(NewObjectIdentifier::class) {
        subclass(NewPredicateIdentifier::class, NewPredicateIdentifier.serializer())
        subclass(NewArrayPredicateIdentifier::class, NewArrayPredicateIdentifier.serializer())
    }
}

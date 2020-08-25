package org.jetbrains.research.kex.state.transformer

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ktype.*
import org.jetbrains.research.kex.smt.SMTModel
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.*
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kfg.type.TypeFactory

enum class Nullability {
    UNKNOWN, NULLABLE, NON_NULLABLE
}

sealed class TypeInfo

data class NullabilityInfo(val nullability: Nullability) : TypeInfo()
data class CastTypeInfo(val type: KexType) : TypeInfo()

class TypeInfoMap(val inner: Map<Term, Set<TypeInfo>> = hashMapOf()) : Map<Term, Set<TypeInfo>> by inner {
    inline fun <reified T : TypeInfo> getInfo(term: Term): T? = inner[term]?.mapNotNull { it as? T }?.also {
        assert(it.size <= 1) { log.warn("A lot of type information ${T::class.qualifiedName} about $term: $it") }
    }?.firstOrNull()

    companion object {
        fun create(tf: TypeFactory, map: Map<Term, Set<TypeInfo>>): TypeInfoMap {
            return TypeInfoMap(
                    map.map { (term, types) ->
                        val reducedTypes = run {
                            val nullabilityInfo = types.filterIsInstance<NullabilityInfo>()
                            val castInfo = types.filterIsInstance<CastTypeInfo>()
                            val reducedCastInfo = mutableSetOf<CastTypeInfo>()
                            val klasses = castInfo.map { (it.type as KexClass).getKfgClass(tf) }.toSet()
                            for (klass in klasses) {
                                if (klasses.any { it != klass && klass.isAncestorOf(it) }) continue
                                else reducedCastInfo += CastTypeInfo(tf.getRefType(klass).kexType)
                            }
                            (nullabilityInfo + reducedCastInfo).toSet()
                        }
                        if (reducedTypes.isEmpty()) null
                        else term to reducedTypes
                    }.filterNotNull().toMap()
            )
        }
    }
}

class TypeInfoCollector(val model: SMTModel, val tf: TypeFactory) : Transformer<TypeInfoCollector> {
    private val typeInfos = mutableMapOf<Term, MutableMap<TypeInfo, PredicateState>>()
    private val cfgt = CFGTracker()

    val infos: TypeInfoMap
        get() = TypeInfoMap.create(
                tf,
                typeInfos.map { (term, map) ->
                    val types = map.filter { checkPath(model, it.value) }.keys
                    term to types
                }.toMap()
        )

    private infix fun PredicateState.or(preds: Set<Predicate>): PredicateState {
        return ChoiceState(listOf(this, BasicState(preds.toList()))).simplify()
    }

    private infix fun PredicateState.or(other: PredicateState): PredicateState {
        return ChoiceState(listOf(this, other)).simplify()
    }

    private infix fun PredicateState.and(preds: Set<Predicate>): PredicateState {
        return ChainState(this, BasicState(preds.toList())).simplify()
    }

    private fun copyInfos(from: Term, to: Term, condition: Set<Predicate>) {
        val fromInfo = typeInfos.getOrElse(from, ::mutableMapOf)
        val toInfos = typeInfos.getOrPut(to, ::mutableMapOf)
        for ((info, conds) in toInfos) {
            val moreCond = fromInfo.getOrDefault(info, emptyState())
            toInfos[info] = conds or (moreCond and condition)
        }
        for ((info, conds) in fromInfo.filter { it.key !in toInfos }) {
            toInfos[info] = conds and condition
        }
    }

    override fun apply(ps: PredicateState): PredicateState {
        cfgt.apply(ps)
        return super.apply(ps)
    }

    override fun transformEquality(predicate: EqualityPredicate): Predicate {
        val condition = cfgt.getDominatingPaths(predicate)
        when (val rhv = predicate.rhv) {
            is InstanceOfTerm -> {
                if (rhv.checkedType !is KexClass) return super.transformEquality(predicate)

                val checkedType = CastTypeInfo(rhv.checkedType)
                val operand = rhv.operand
                val fullPath = condition + path { predicate.lhv equality true }

                val typeInfo = typeInfos.getOrPut(operand, ::mutableMapOf)
                val existingCond = typeInfo.getOrDefault(checkedType, emptyState())
                typeInfo[checkedType] = existingCond or fullPath
            }
            is PrimitiveCastTerm -> {
                // never class type
            }
            is FieldLoadTerm -> copyInfos(rhv.field, predicate.lhv, condition)
            is ArrayLoadTerm -> copyInfos(rhv.arrayRef, predicate.lhv, condition)
            else -> copyInfos(rhv, predicate.lhv, condition)
        }
        return super.transformEquality(predicate)
    }

    override fun transformCast(predicate: CastPredicate): Predicate {
        val condition = cfgt.getDominatingPaths(predicate)
        if (predicate.operandType !is KexClass) return super.transformCast(predicate)
        val newType = CastTypeInfo(predicate.operandType)
        val operand = predicate.operand
        val stub = when {
            condition.isEmpty() -> setOf(path { const(true) equality true })
            else -> condition
        }

        // we can't do anything with primary type casts
        if (newType.type is KexIntegral || newType.type is KexReal) return predicate

        val typeInfo = typeInfos.getOrPut(operand, ::mutableMapOf)
        val existingCond = typeInfo.getOrDefault(newType, emptyState())
        typeInfo[newType] = existingCond or stub

        return super.transformCast(predicate)
    }

    override fun transformInequality(predicate: InequalityPredicate): Predicate {
        when (predicate.rhv) {
            is NullTerm -> {
                val nullability = NullabilityInfo(Nullability.NON_NULLABLE)
                val condition = cfgt.getDominatingPaths(predicate)
                val lhv = predicate.lhv

                val typeInfo = typeInfos.getOrPut(lhv, ::mutableMapOf)
                val existingCond = typeInfo.getOrDefault(nullability, emptyState())
                typeInfo[nullability] = existingCond or condition
            }
        }
        return super.transformInequality(predicate)
    }

    override fun transformFieldStore(predicate: FieldStorePredicate): Predicate {
        copyInfos(predicate.value, predicate.field, cfgt.getDominatingPaths(predicate))
        return super.transformFieldStore(predicate)
    }

    override fun transformArrayStore(predicate: ArrayStorePredicate): Predicate {
        copyInfos(predicate.value, predicate.arrayRef, cfgt.getDominatingPaths(predicate))
        return super.transformArrayStore(predicate)
    }
}

class PlainTypeInfoCollector(val tf: TypeFactory) : Transformer<TypeInfoCollector> {
    private val typeInfos = mutableMapOf<Term, MutableSet<TypeInfo>>()

    val infos: TypeInfoMap
        get() = TypeInfoMap.create(tf, typeInfos)

    override fun transformEquality(predicate: EqualityPredicate): Predicate {
        when (val rhv = predicate.rhv) {
            is InstanceOfTerm -> {
                val checkedType = CastTypeInfo(rhv.checkedType)
                val operand = rhv.operand

                val typeInfo = typeInfos.getOrPut(operand, ::mutableSetOf)
                typeInfo += checkedType
            }
            is PrimitiveCastTerm -> {
                val newType = CastTypeInfo(rhv.type)
                val operand = rhv.operand

                // we can't do anything with primary type casts
                if (newType.type is KexIntegral || newType.type is KexReal) return predicate

                val typeInfo = typeInfos.getOrPut(operand, ::mutableSetOf)
                typeInfo += newType
            }
        }
        return super.transformEquality(predicate)
    }

    override fun transformCast(predicate: CastPredicate): Predicate {
        val newType = CastTypeInfo(predicate.operandType)
        val operand = predicate.operand

        // we can't do anything with primary type casts
        if (newType.type is KexIntegral || newType.type is KexReal) return predicate

        val typeInfo = typeInfos.getOrPut(operand, ::mutableSetOf)
        typeInfo += newType
        return super.transformCast(predicate)
    }

    override fun transformInequality(predicate: InequalityPredicate): Predicate {
        when (predicate.rhv) {
            is NullTerm -> {
                val nullability = NullabilityInfo(Nullability.NON_NULLABLE)
                val lhv = predicate.lhv

                val typeInfo = typeInfos.getOrPut(lhv, ::mutableSetOf)
                typeInfo += nullability
            }
        }
        return super.transformInequality(predicate)
    }
}

fun collectTypeInfos(model: SMTModel, tf: TypeFactory, ps: PredicateState): TypeInfoMap {
    val tic = TypeInfoCollector(model, tf)
    tic.apply(ps)
    return tic.infos
}

fun collectPlainTypeInfos(tf: TypeFactory, ps: PredicateState): TypeInfoMap {
    val tic = PlainTypeInfoCollector(tf)
    tic.apply(ps)
    return tic.infos
}
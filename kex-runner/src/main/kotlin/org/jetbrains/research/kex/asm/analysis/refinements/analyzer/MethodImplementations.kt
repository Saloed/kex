package org.jetbrains.research.kex.asm.analysis.refinements.analyzer

import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.*
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.util.VariableGenerator
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.UnknownInstance
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass

open class MethodImplementationMerge(val method: Method) {
    open val baseGenerator: VariableGenerator
        get() = VariableGenerator("inheritance")
    val pathGenerator: VariableGenerator
        get() = baseGenerator.createNestedGenerator("path")
    val tmpGenerator: VariableGenerator
        get() = baseGenerator.createNestedGenerator("tmp")
    val owner: Term
        get() = term { `this`(method.`class`.kexType) }

    open fun mapUnmappedTerm(method: Method, term: Term): Term? = if (term is ArgumentTerm) term else null
    open fun createInstanceOf(term: Term, type: KexType) = term { tf.getInstanceOf(type, term) }
    open fun createCast(builder: PredicateBuilder, lhs: Term, term: Term, type: KexType) = builder.pf.getCast(lhs, term, type, builder.type, builder.location)

    fun mergeImplementations(
            implementations: List<Pair<PredicateStateWithPath, Method>>
    ): PredicateStateWithPath {
        val result = pathGenerator.generatorFor("result").createVar(KexBool())
        val types = implementations.map { it.second }.map { it.`class`.kexType }
        val (typeBindings, typeMapping) = typeChecks(types, tmpGenerator.createNestedGenerator("type"))
        val states = implementations.mapIndexed { index, ref ->
            val myType = types[index]
            val myTypeVariable = typeMapping.getValue(types[index])
            val otherTypeVariables = typeMapping.filterKeys { it != myType }.values.toList()
            withMethodInfo(
                    ref.first, ref.second, result,
                    myType, myTypeVariable, otherTypeVariables,
                    tmpGenerator.createNestedGenerator("$index")
            )
        }
        val typeGuard = basic {
            assume { typeMapping.values.toList().combine(false) { a, b -> a or b } equality true }
        }
        val mergedState = chain(listOf(typeBindings, typeGuard, ChoiceState(states)))
        val mergedPath = basic { path { result equality true } }
        return PredicateStateWithPath(mergedState, mergedPath)
    }

    private fun typeChecks(
            types: List<KexType>,
            variableGenerator: VariableGenerator
    ): Pair<PredicateState, Map<KexType, Term>> {
        val generator = variableGenerator.unique()
        val (predicates, variables) = types
                .map { createInstanceOf(owner, it) }
                .map {
                    val variable = generator.createUniqueVar(KexBool())
                    state { variable equality it } to variable
                }
                .unzip()
        val state = BasicState(predicates)
        return state to types.zip(variables).toMap()
    }

    private fun withMethodInfo(
            stateWithPath: PredicateStateWithPath,
            method: Method, result: Term,
            type: KexType, typeVariable: Term,
            otherTypeVariables: List<Term>,
            generator: VariableGenerator): PredicateState {
        val thisTerm = generator.generatorFor("this").createVar(type)
        val oldThisTerm = term { tf.getThis(type) }
        val mapper = TermMapper(generator, mapOf(oldThisTerm to thisTerm)) {
            mapUnmappedTerm(method, it)
        }
        val newState = mapper.apply(stateWithPath.state)
        val pathTerm = mapper.apply(stateWithPath.path).asTerm()
        val castState = basic {
            path { typeVariable equality true }
            otherTypeVariables.forEach {
                path { it equality false }
            }
            state { createCast(this, thisTerm, owner, type) }
        }
        val pathState = basic {
            state { result equality pathTerm }
        }
        return chain(listOf(castState, newState, pathState))
    }

    private fun PredicateState.asTerm(): Term = when (this) {
        is BasicState -> predicates.map { it.asTerm() }.combine(true) { a, b -> a and b }
        is ChainState -> listOf(base, curr).map { it.asTerm() }.combine(true) { a, b -> a and b }
        is ChoiceState -> choices.map { it.asTerm() }.combine(false) { a, b -> a or b }
        is NegationState -> term { predicateState.asTerm().not() }
        else -> error("No term convertion for state $this")
    }

    private fun Predicate.asTerm(): Term = when (this) {
        is EqualityPredicate -> when {
            rhv is ConstBoolTerm -> if ((rhv as ConstBoolTerm).value) lhv else term { lhv.not() }
            lhv is ConstBoolTerm -> if ((lhv as ConstBoolTerm).value) rhv else term { rhv.not() }
            else -> term { lhv eq rhv }
        }
        is ConstantPredicate -> term { const(value) }
        else -> error("No term convertion for predicate $this")
    }

    private fun List<Term>.combine(default: Boolean, operation: TermBuilder.(Term, Term) -> Term) =
            reduceOrNull { acc, term -> term { operation(acc, term) } } ?: term { const(default) }

}

class MethodImplementations(private val cm: ClassManager, private val methodRefinements: MethodRefinements) {
    fun collectImplementations(method: Method): Set<Method> =
            collectInheritors(method.`class`)
                    .mapNotNull { it.getMethodOrNull(method) }
                    .toSet()

    private fun collectInheritors(cls: Class): Set<Class> = when (cls) {
        is OuterClass -> emptySet()
        else -> cm.concreteClasses
                .filter { it.isInheritorOf(cls) }
                .filterNot { methodRefinements.isExcluded(it) }
                .toSet()
    }

    private fun Class.getMethodOrNull(method: Method) = try {
        getMethod(method.name, method.desc)
    } catch (ex: UnknownInstance) {
        null
    }?.let {
        when {
            it.isEmpty() -> null
            else -> it
        }
    }

}

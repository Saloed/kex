package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method

import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.analysis.refinements.Refinement
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.TermMapper
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.MethodFunctionalInliner
import org.jetbrains.research.kex.util.VariableGenerator
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.UnknownInstance
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass

class OpenMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {
    override fun analyze(): Refinements {
        val implementations = collectImplementations(method)
        val refinements = implementations.map {
            when (it) {
                method -> NoInliningSimpleMethodAnalyzer(cm, psa, refinementsManager, it).analyze()
                else -> findRefinement(it)
            }
        }
        return when (refinements.size) {
            1 -> refinements.first()
            0 -> TODO("empty implementations")
            else -> mergeRefinements(refinements)
        }
    }

    private fun mergeRefinements(refinements: List<Refinements>) = refinements
            .flatMap { ref -> ref.value.map { it to ref.method } }
            .groupBy { it.first.criteria }
            .mapValues { it.value.map { (ref, method) -> ref.state to method } }
            .mapValues { mergeRefinements(it.value) }
            .mapValues { Refinement.create(it.key, it.value) }
            .let { Refinements.create(method, it.values.toList()) }

    private fun mergeRefinements(refinements: List<Pair<PredicateStateWithPath, Method>>): PredicateStateWithPath {
        val variableGenerator = VariableGenerator("inheritance")
        val result = variableGenerator.generatorFor("result").createVar(KexBool())
        val owner = term { `this`(method.`class`.kexType) }
        val types = refinements.map { it.second }.map { it.`class`.kexType }
        val (typeBindings, typeMapping) = typeChecks(owner, types, variableGenerator.createNestedGenerator("type"))
        val states = refinements.mapIndexed { index, ref ->
            val myType = types[index]
            val myTypeVariable = typeMapping.getValue(types[index])
            val otherTypeVariables = typeMapping.filterKeys { it != myType }.values.toList()
            ref.first.withMethodInfo(
                    owner, result,
                    myType, myTypeVariable, otherTypeVariables,
                    variableGenerator.createNestedGenerator("$index")
            )
        }
        val typeGuard = basic {
            assume { typeMapping.values.toList().combine(false) { a, b -> a or b } equality true }
        }
        val mergedState = chain(listOf(typeBindings, typeGuard, ChoiceState(states)))
        val mergedPath = basic { path { result equality true } }
        return PredicateStateWithPath(mergedState, mergedPath)
    }

    private fun typeChecks(owner: Term, types: List<KexType>, variableGenerator: VariableGenerator): Pair<PredicateState, Map<KexType, Term>> {
        val generator = variableGenerator.unique()
        val (predicates, variables) = types
                .map { term { tf.getInstanceOf(it, owner) } }
                .map {
                    val variable = generator.createUniqueVar(KexBool())
                    state { variable equality it } to variable
                }
                .unzip()
        val state = BasicState(predicates)
        return state to types.zip(variables).toMap()
    }

    private fun PredicateStateWithPath.withMethodInfo(
            owner: Term,
            result: Term,
            type: KexType,
            typeVariable: Term,
            otherTypeVariables: List<Term>,
            generator: VariableGenerator
    ): PredicateState {
        val thisTerm = generator.generatorFor("this").createVar(type)
        val oldThisTerm = term { tf.getThis(type) }
        val mapper = TermMapper(generator, mapOf(oldThisTerm to thisTerm)) {
            if (it is ArgumentTerm) it else null
        }
        val newState = mapper.apply(state)
        val pathTerm = mapper.apply(path).asTerm()
        val castState = basic {
            path { typeVariable equality true }
            otherTypeVariables.forEach {
                path { it equality false }
            }
            state { pf.getCast(thisTerm, owner, type) }
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
        else -> error("No term convertion for predicate $this")
    }

    private fun List<Term>.combine(default: Boolean, operation: TermBuilder.(Term, Term) -> Term) =
            reduceOrNull { acc, term -> term { operation(acc, term) } } ?: term { const(default) }


    override fun MethodFunctionalInliner.TransformationState.getMethodStateAndRefinement() = error("Unavailable")


    private fun collectImplementations(method: Method): Set<Method> =
            collectInheritors(method.`class`)
                    .mapNotNull { it.getMethodOrNull(method) }
                    .toSet()


    private fun collectInheritors(cls: Class): Set<Class> = when (cls) {
        is OuterClass -> emptySet()
        else -> cm.concreteClasses
                .filter { it.isInheritorOf(cls) }
                .filterNot { refinementsManager.isExcluded(it) }
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

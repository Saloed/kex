package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.*
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.transform
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method

class CallInliner(
        val rootMethod: Method,
        val psa: PredicateStateAnalysis,
        val refinementProvider: RefinementProvider
) : RecollectingTransformer<CallInliner> {
    override val builders = dequeOf(StateBuilder())
    private val refinementVariableGenerator = VariableGenerator("refinement")
    private val methodVariableGenerator = VariableGenerator("method")
    val callPathConditions = hashMapOf<CallPredicate, Map<RefinementCriteria, List<Term>>>()

    override fun transformCall(predicate: CallPredicate): Predicate {
        val argumentMapping = MethodManager.InlineManager.methodArguments(predicate)
        val refinement = refinementProvider.findRefinement(predicate.method())
        val pathConditions = refinement.createPathVariables(argumentMapping, refinementVariableGenerator.generatorFor(predicate))
        callPathConditions[predicate] = pathConditions
        return super.transformCall(predicate)
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val varGenerator = methodVariableGenerator.generatorFor(predicate)
        val pathConditions = callPathConditions[predicate] ?: error("Path conditions are not computed")
        pathConditions.values.flatten().map { pc ->
            EqualityPredicate(pc, term { const(false) }, PredicateType.Path(), predicate.location)
        }.forEach { currentBuilder += it }
        val method = predicate.method()
        val inlineStatus = MethodManager.InlineManager.isInlinable(method)
        if (inlineStatus != MethodManager.InlineManager.InlineStatus.INLINE) return predicate
        val argumentMapping = MethodManager.InlineManager.methodArguments(predicate)
        return when {
            method.isConstructor -> inlineConstructor(predicate, method, varGenerator, argumentMapping)
            else -> inlineSimple(predicate, method, varGenerator, argumentMapping)
        }
    }

    private fun inlineSimple(predicate: CallPredicate, method: Method, varGenerator: VariableGenerator, argumentMapping: Map<Term, Term>): Predicate {
        if (method.isEmpty()) return predicate
        val methodState = psa.builder(method).methodState ?: return predicate
        val state = TermMapper(varGenerator.createNestedGenerator("inlined"), argumentMapping).apply(methodState)
        val nestedCalls = PredicateCollector.collectIsInstance<CallPredicate>(state)
        if (nestedCalls.isNotEmpty()) return predicate
        currentBuilder += state
        return nothing()
    }

    private fun inlineConstructor(predicate: CallPredicate, method: Method, varGenerator: VariableGenerator, argumentMapping: Map<Term, Term>): Predicate {
        if (method.isEmpty()) return when {
            isObjectConstructor(method) -> nothing()
            else -> predicate
        }
        val constructorState = psa.builder(method).methodState ?: return predicate
        val inliner = CallInliner(method, psa, refinementProvider)
        val refinementVarGenerator = refinementVariableGenerator.generatorFor(predicate).createNestedGenerator("constructor_pc")
        val pcVarMapping = hashMapOf<Term, Term>()
        val currentPathConditions = callPathConditions.getValue(predicate)
        val pathConditionExtension = inliner.callPathConditions.values
                .flatMap { it.flatPathConditions() }
                .map { (criteria, term) ->
                    val newTerm = refinementVarGenerator.generatorFor(term).createVar(term.type)
                    pcVarMapping[term] = newTerm
                    criteria to term
                }
                .plus(currentPathConditions.flatPathConditions())
                .groupBy({ it.first }, { it.second })
        callPathConditions[predicate] = currentPathConditions + pathConditionExtension
        val constructorStateResolved = inliner.apply(constructorState)
        val state = TermMapper(varGenerator.createNestedGenerator("constructor"), argumentMapping + pcVarMapping).apply(constructorStateResolved)
        currentBuilder += state
        return nothing()
    }

    private fun Map<RefinementCriteria, List<Term>>.flatPathConditions() = entries.flatMap { (criteria, terms) -> terms.map { criteria to it } }

    private fun CallPredicate.method() = (call as CallTerm).method
    private fun CallPredicate.instruction() = (call as CallTerm).instruction

    private fun Refinements.createPathVariables(argumentMapping: Map<Term, Term>, generator: VariableGenerator): Map<RefinementCriteria, List<Term>> {
        val varGenerator = generator.createNestedGenerator("pc")
        return value.map { it.createPathVariable(varGenerator.generatorFor(it), argumentMapping) }.toMap()
    }

    private fun Refinement.createPathVariable(varGenerator: VariableGenerator, argumentMapping: Map<Term, Term>): Pair<RefinementCriteria, List<Term>> {
        val argumentMapper = TermMapper(varGenerator.createNestedGenerator("var"), argumentMapping)
        val pathPredicateTransformer = PathPredicateToPathVariableTransformer(varGenerator.createNestedGenerator("pv"))
        currentBuilder += transform(state) {
            +argumentMapper
            +pathPredicateTransformer
        }
        val pathVariable = varGenerator.generatorFor(this).createVar(KexBool())
        val pathCondition = term { pathPredicateTransformer.createdPathVars.reduce { acc, term -> acc and term } }
        currentBuilder += EqualityPredicate(pathVariable, pathCondition)
        return criteria to listOf(pathVariable)
    }

    private fun isObjectConstructor(method: Method): Boolean {
        if (!method.isConstructor) return false
        return isJavaInlineable(method.`class`) || isKotlinInlineable(method.`class`)
    }

    private fun isKotlinInlineable(cls: Class): Boolean {
        if (cls.`package` != KOTLIN_PACKAGE) return false
        if (cls.name == "Any") return true
        return false
    }

    private fun isJavaInlineable(cls: Class): Boolean {
        if (cls.`package` != JAVA_PACKAGE) return false
        if (cls.name == "Object") return true
        if (cls.name.endsWith("Exception")) return true
        return false
    }

    companion object {
        private val JAVA_PACKAGE = Package.parse("java/lang")
        private val KOTLIN_PACKAGE = Package.parse("kotlin")
    }

}

private class TermMapper(val variableGenerator: VariableGenerator, val mapping: Map<Term, Term>) : Transformer<TermMapper> {
    override fun transformTerm(term: Term): Term = mapping[term] ?: when (term) {
        is ValueTerm, is ArgumentTerm, is ReturnValueTerm -> variableGenerator.generatorFor(term).createVar(term.type)
        else -> term
    }
}

private class PathPredicateToPathVariableTransformer(val variableGenerator: VariableGenerator) : Transformer<PathPredicateToPathVariableTransformer> {
    val createdPathVars = arrayListOf<Term>()

    override fun transformPredicate(predicate: Predicate): Predicate {
        if (predicate.type != PredicateType.Path()) return super.transformPredicate(predicate)
        val pathVar = variableGenerator.generatorFor(predicate).createVar(KexBool())
        createdPathVars += pathVar
        val pathCondition = when (predicate) {
            is EqualityPredicate -> term { predicate.lhv eq predicate.rhv }
            is InequalityPredicate -> term { predicate.lhv neq predicate.rhv }
            else -> error("Unsupported predicate $predicate")
        }
        return EqualityPredicate(pathVar, pathCondition, PredicateType.State(), predicate.location)
    }

}

private class VariableGenerator(val prefix: String) {
    private var generatorIndex: Int = 0
    private val indexMapping = hashMapOf<Any, Int>()
    fun generatorFor(obj: Any): VariableGenerator {
        val idx = indexMapping.getOrPut(obj) { generatorIndex++ }
        return VariableGenerator("${prefix}_${idx}")
    }
    fun createVar(type: KexType) = term { value(type, prefix) }
    fun createNestedGenerator(prefix: String) = VariableGenerator("${this.prefix}_${prefix}")
}

package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kex.util.VariableGenerator
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method

class CallInliner(
        val cm: ClassManager,
        val psa: PredicateStateAnalysis,
        val refinementProvider: RefinementProvider,
        val forceDeepInline: Boolean = false,
) : RecollectingTransformer<CallInliner> {
    override val builders = dequeOf(StateBuilder())
    private val refinementVariableGenerator = VariableGenerator("refinement")
    private val methodVariableGenerator = VariableGenerator("method")
    val callPathConditions = hashMapOf<CallPredicate, PathConditions>()

    override fun transformCall(predicate: CallPredicate): Predicate {
        val argumentMapping = MethodManager.InlineManager.methodArguments(predicate)
        val refinement = refinementProvider.findRefinement(predicate.method())
        val pathConditions = refinement.createPathVariables(argumentMapping, refinementVariableGenerator.generatorFor(predicate))
        callPathConditions[predicate] = pathConditions
        return super.transformCall(predicate)
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val varGenerator = methodVariableGenerator.generatorFor(predicate)
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
        val methodState = methodState(method) ?: return predicate
        val nestedCalls = PredicateCollector.collectIsInstance<CallPredicate>(methodState)
        if (nestedCalls.isNotEmpty() && !forceDeepInline) return predicate
        return inlineNestedCalls(methodState, "method", predicate, varGenerator, argumentMapping)
    }

    private fun inlineConstructor(predicate: CallPredicate, method: Method, varGenerator: VariableGenerator, argumentMapping: Map<Term, Term>): Predicate {
        if (method.isEmpty()) return when {
            isObjectConstructor(method) -> nothing()
            else -> predicate
        }
        val constructorState = methodState(method) ?: return predicate
        return inlineNestedCalls(constructorState, "constructor", predicate, varGenerator, argumentMapping)
    }

    private fun methodState(method: Method): PredicateState? {
        val methodExecutionPaths = MethodExecutionPathsAnalyzer(cm, psa, method)
        if (methodExecutionPaths.isEmpty) return null
        return methodExecutionPaths.methodRawFullState()
    }

    private fun inlineNestedCalls(methodState: PredicateState, prefix: String, predicate: CallPredicate, varGenerator: VariableGenerator, argumentMapping: Map<Term, Term>): Predicate {
        val inliner = CallInliner(cm, psa, refinementProvider, forceDeepInline = false)
        val stateResolved = inliner.apply(methodState)
        val refinementVarGenerator = refinementVariableGenerator.generatorFor(predicate).createNestedGenerator("${prefix}_pc")
        val pcVarMapping = hashMapOf<Term, Term>()
        val pathConditionExtension = inliner.callPathConditions.values.map { pathConditions ->
            pathConditions.fmap { _, pcState ->
                val variables = collectVariables(pcState)
                val varMapping = variables.associateWith { pv ->
                    val newTerm = refinementVarGenerator.generatorFor(pv).createVar(pv.type)
                    pcVarMapping[pv] = newTerm
                    newTerm
                }
                TermMapper(refinementVariableGenerator, varMapping).apply(pcState)
            }
        }
        callPathConditions[predicate] = callPathConditions[predicate]?.merge(pathConditionExtension)
                ?: error("No path conditions for predicate $predicate")
        val state = TermMapper(varGenerator.createNestedGenerator(prefix), argumentMapping + pcVarMapping).apply(stateResolved)
        currentBuilder += state
        return nothing()
    }

    private fun CallPredicate.method() = (call as CallTerm).method

    private fun Refinements.createPathVariables(argumentMapping: Map<Term, Term>, generator: VariableGenerator): PathConditions {
        val varGenerator = generator.createNestedGenerator("pc")
        val pathConditions = value.map { it.createPathVariable(varGenerator.generatorFor(it), argumentMapping) }
        return PathConditions(emptyMap()).merge(pathConditions)
    }

    private fun Refinement.createPathVariable(varGenerator: VariableGenerator, argumentMapping: Map<Term, Term>): PathConditions {
        val argumentMapper = TermMapper(varGenerator.createNestedGenerator("var"), argumentMapping)
        val preparedState = state.accept(argumentMapper::apply)
        return when {
            preparedState.state.evaluatesToFalse || preparedState.path.evaluatesToFalse -> PathConditions(emptyMap())
            preparedState.state.evaluatesToTrue || preparedState.path.evaluatesToTrue -> {
                log.warn("Inline call refinement which is always true")
                currentBuilder += preparedState.negate().toPredicateState()
                PathConditions(emptyMap())
            }
            else -> {
                currentBuilder += preparedState.state
                PathConditions(mapOf(criteria to preparedState.path))
            }
        }
    }

    override fun apply(ps: PredicateState): PredicateState {
        val intrinsicsResolved = IntrinsicAdapter.apply(ps)
        return super.apply(intrinsicsResolved)
    }

    companion object {
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
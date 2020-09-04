package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.MethodExecutionPathsAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.RefinementSources
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.sources.RefinementSourcesAnalyzer
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.UnknownInstance
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass
import ru.spbstu.ktuples.zip

class SimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    private val methodImplementations = hashMapOf<Method, List<Method>>()

    override fun analyze(): Refinements {
        val methodPaths = MethodExecutionPathsAnalyzer(cm, psa, method)
        val state = buildMethodState(methodPaths)
        val refinementSources = methodPaths.exceptionalExecutionPaths
        val normalPaths = methodPaths.normalExecutionPaths
        val (nestedNormal, nestedRefinementSources) = inlineRefinements()

        val allSources = refinementSources.merge(nestedRefinementSources).fmap { it.optimize() }
        val allNormal = ChainState(normalPaths, nestedNormal).optimize()

        val (spacedState, spacesSources, spacedNormal) = applyMemspacing(state, allSources, allNormal)

        log.info("Analyze: $method")
        log.debug("State:\n$spacedState\nExceptions:\n$spacesSources\nNormal:\n$spacedNormal")
        return RefinementSourcesAnalyzer(this).analyze(spacedState, spacedNormal, spacesSources, MemoryVersionInfo(emptyMap(), emptyMap()))
    }

    override fun findRefinement(method: Method): Refinements {
        val implementations = methodImplementations[method] ?: return super.findRefinement(method)
        if (implementations.isEmpty()) return super.findRefinement(method)
        val implementationsRefinements = implementations.map { super.findRefinement(it) }
        return zip(implementations, implementationsRefinements)
                .map { (impl, reft) ->
                    transformToMethodImplementation(method.`class`.kexType, impl) { transformer ->
                        reft.fmap {
                            val state = transformer(it.state)
                            PredicateStateWithPath(state, it.path)
                        }
                    }
                }
                .reduce { a, b -> a.merge(b) }
    }


    override fun MethodFunctionalInliner.TransformationState.getMethodStateAndRefinement(): Pair<Refinements, PredicateState> {
        val methodState = getStateForInlining()
        if (methodState != null) return findRefinement(calledMethod).expanded() to methodState

        fun noState(): Pair<Refinements, PredicateState> {
            val refinement = findRefinement(calledMethod).expanded()
            return when {
                refinement.isUnknown() -> skip()
                else -> refinement to BasicState()
            }
        }

        if (!inliningIsPossible()) return noState()

        val type = call.owner.type as? KexClass ?: return noState()
        val implementations = methodImplementations.getOrPut(calledMethod) {
            collectImplementations(type, calledMethod).filterNot { it.isEmpty() }
        }
        val implementationStates = implementations.map { psa.builder(it).methodState }
        val implementationChoices = arrayListOf<PredicateState>()
        for ((implementation, methodImplState) in zip(implementations, implementationStates)) {
            if (methodImplState == null) continue
            implementationChoices += transformToMethodImplementation(type, implementation) { it(methodImplState) }
        }
        return when {
            implementationChoices.isEmpty() -> noState()
            else -> findRefinement(calledMethod).expanded() to ChoiceState(implementationChoices)
        }
    }


    private fun applyMemspacing(state: PredicateState, allSources: RefinementSources, allNormal: PredicateState): Triple<PredicateState, RefinementSources, PredicateState> {
        val allStates = listOf(state) + allSources.value.map { it.condition } + listOf(allNormal)
        val memorySpacer = MemorySpacer(ChoiceState(allStates))
        val newState = memorySpacer.apply(state)
        val newSources = allSources.fmap { memorySpacer.apply(it) }
        val newNormal = memorySpacer.apply(allNormal)
        return Triple(newState, newSources, newNormal)
    }

    private inline fun <reified T> transformToMethodImplementation(type: KexType, implementation: Method, transformSource: ((PredicateState) -> PredicateState) -> T): T =
            transformSource {
                val owner = buildOwnerTypeChecks(implementation, type)
                val methodState = castMethodOwnerType(implementation, it, type)
                ChainState(owner, methodState)
            }

    private fun buildOwnerTypeChecks(method: Method, type: KexType) = basic {
        path {
            tf.getInstanceOf(method.`class`.kexType, tf.getThis(type)) equality const(true)
        }
    }

    private fun castMethodOwnerType(method: Method, methodState: PredicateState, type: KexType): PredicateState {
        val newType = method.`class`.kexType
        val currentThis = term { tf.getThis(type) }
        val castedThis = term { value(newType, "this_as_${newType.name}") }
        val castState = state {
            castedThis.cast(currentThis, newType)
        }
        val mapped = transform(methodState) {
            +TermRemapper(mapOf(currentThis to castedThis))
        }
        return ChainState(castState.wrap(), mapped)
    }

    private fun collectImplementations(cls: KexClass, method: Method): Set<Method> =
            collectInheritors(cls.kfgClass(cm.type))
                    .mapNotNull { it.getMethodOrNull(method) }
                    .filterNot { it == this.method } // fixme: recursive implementations skipped
                    .toSet()

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

    private fun collectInheritors(cls: Class): Set<Class> = when (cls) {
        is OuterClass -> emptySet()
        else -> cm.concreteClasses
                .filter { it.isInheritorOf(cls) }
                .filterNot { refinementsManager.isExcluded(it) }
                .toSet()
    }

}

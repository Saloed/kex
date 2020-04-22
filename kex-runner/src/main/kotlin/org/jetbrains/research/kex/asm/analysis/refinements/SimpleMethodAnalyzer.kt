package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kex.util.join
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.UnknownInstance
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass
import ru.spbstu.ktuples.zip

class SimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    private val methodImplementations = hashMapOf<Method, List<Method>>()

    override fun analyze(): Refinements {
        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, method)
        val state = buildMethodState(methodPaths)
        val refinementSources = methodPaths.refinementSources
        val normalPaths = methodPaths.normalExecutionPaths
        val (nestedNormal, nestedRefinementSources) = inlineRefinements()

        val allSources = refinementSources.merge(nestedRefinementSources).fmap { it.optimize() }
        val allNormal = ChainState(normalPaths, nestedNormal).optimize()
//        val allNormal = allSources.fmap { it.negateWRTStatePredicates() }.fmap { normalPaths + it }.fmap { it.optimize() }

        val (spacedState, spacesSources, spacedNormal) = applyMemspacing(state, allSources, allNormal)

        log.info("Analyze: $method")
        log.debug("State:\n$spacedState\nExceptions:\n$spacesSources\nNormal:\n$spacedNormal")

        val (trivialRefinements, sourcesToQuery) = searchForDummySolution(spacedNormal, spacesSources)
        val otherRefinements = queryRefinementSources(spacedState, spacedNormal, sourcesToQuery)

        return Refinements.create(method, trivialRefinements.value + otherRefinements.value).fmap { transform(it) { applyAdapters() } }
    }

    override fun findRefinement(method: Method): Refinements {
        val implementations = methodImplementations[method] ?: return super.findRefinement(method)
        if (implementations.isEmpty()) return super.findRefinement(method)
        val implementationsRefinements = implementations.map { super.findRefinement(it) }
        return zip(implementations, implementationsRefinements)
                .map { (impl, reft) -> transformToMethodImplementation(method.`class`.kexType, impl, reft::fmap) }
                .join { a, b -> a.merge(b) }
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

    private fun castMethodOwnerType(method: Method, state: PredicateState, type: KexType): PredicateState {
        val currentThis = term { tf.getThis(type) }
        val castedThis = term { tf.getCast(method.`class`.kexType, currentThis) }
        return transform(state) {
            +TermRemapper(mapOf(currentThis to castedThis))
        }
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

    private fun searchForDummySolution(normals: PredicateState, exceptions: RefinementSources): Pair<Refinements, RefinementSources> {
        val sourcesToQuery = mutableListOf<RefinementSource>()
        val dummyRefinements = mutableListOf<Refinement>()
        for (source in exceptions.value) {
            val dummyResult = analyzeForDummyResult(normals, source.condition)
            if (dummyResult == null) {
                sourcesToQuery.add(source)
                continue
            }
            dummyRefinements.add(Refinement.create(source.criteria, dummyResult))
        }
        return Refinements.create(method, dummyRefinements) to RefinementSources.create(sourcesToQuery)
    }

    private fun analyzeForDummyResult(normalPaths: PredicateState, exceptionPaths: PredicateState): PredicateState? = when {
        normalPaths.evaluatesToTrue && exceptionPaths.evaluatesToFalse -> falseState()
        normalPaths.evaluatesToFalse && exceptionPaths.evaluatesToTrue -> trueState()
        normalPaths.evaluatesToTrue && exceptionPaths.evaluatesToTrue -> {
            log.error("Normal and Exception paths are always true")
            falseState()
        }
        normalPaths.evaluatesToFalse && exceptionPaths.evaluatesToFalse -> {
            log.error("Normal and Exception paths are always false")
            falseState()
        }
        else -> null
    }

    private fun queryRefinementSources(state: PredicateState, normals: PredicateState, sources: RefinementSources): Refinements {
        if (sources.value.isEmpty()) return Refinements.unknown(method)
        val conditions = sources.value.map { it.condition }
        val fixpointAnswer = queryFixpointSolver(state, normals, conditions)
//        val fixpointAnswer = conditions.map { src -> queryFixpointSolver(state, normals, listOf(src)).first() }
        val refinements = sources.value.zip(fixpointAnswer).map { (src, answer) -> Refinement.create(src.criteria, answer) }
        return Refinements.create(method, refinements)
    }

    private fun queryFixpointSolver(state: PredicateState, normal: PredicateState, exceptions: List<PredicateState>): List<PredicateState> =
            try {
                val result = Z3FixpointSolver(cm.type).mkFixpointQuery(state, exceptions, normal)
                when (result) {
                    is FixpointResult.Sat -> result.result
                    is FixpointResult.Unknown -> {
                        log.error("Unknown: ${result.reason}")
                        exceptions.map { falseState() }
                    }
                    is FixpointResult.Unsat -> {
                        log.error("Unsat: ${result.core.contentToString()}")
                        exceptions.map { falseState() }
                    }
                }
            } catch (ex: QueryCheckStatus.FixpointQueryException) {
                log.error("Bad fixpoint query: ${ex.status}")
                exceptions.map { falseState() }
            }
}

package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
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
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kex.util.join
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.UnknownInstance
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass
import ru.spbstu.ktuples.zip

class NoInliningSimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    private val methodImplementations = hashMapOf<Method, List<Method>>()

    override fun analyze(): Refinements {
        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, method)
        val state = extendWithRefinements(methodPaths)
        val refinementSources = methodPaths.refinementSources
        val normalPaths = methodPaths.normalExecutionPaths
        val (nestedNormal, nestedRefinementSources) = inlineRefinementsV2(state)

        val allSources = refinementSources.merge(nestedRefinementSources).fmap { it.optimize() }
        val allNormal = ChainState(normalPaths, nestedNormal).optimize()

        val (spacedState, spacesSources, spacedNormal) = applyMemspacing(state, allSources, allNormal)

        log.info("Analyze: $method")
        log.debug("State:\n$spacedState\nExceptions:\n$spacesSources\nNormal:\n$spacedNormal")

        val (trivialRefinements, sourcesToQuery) = searchForDummySolution(spacedNormal, spacesSources)
        val otherRefinements = queryRefinementSources(spacedState, spacedNormal, sourcesToQuery)

        return Refinements.create(method, trivialRefinements.value + otherRefinements.value).fmap { transform(it) { applyAdapters() } }
    }


    override fun MethodFunctionalInliner.TransformationState.getMethodStateAndRefinement(): Pair<Refinements, PredicateState> {
        TODO("Not yet implemented")
    }

    override fun findRefinement(method: Method): Refinements {
        val implementations = methodImplementations[method] ?: return super.findRefinement(method)
        if (implementations.isEmpty()) return super.findRefinement(method)
        val implementationsRefinements = implementations.map { super.findRefinement(it) }
        return zip(implementations, implementationsRefinements)
                .map { (impl, reft) -> transformToMethodImplementation(method.`class`.kexType, impl, reft::fmap) }
                .join { a, b -> a.merge(b) }
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

    private fun extendWithRefinements(builder: MethodRefinementSourceAnalyzer): PredicateState {
        val originalState = builder.methodRawFullState()
        val calls = PredicateCollector.collectIsInstance<CallPredicate>(originalState)
        val exceptionalPaths = calls.map { predicate ->
            val instructionState = psa.builder(method).getInstructionState(predicate.instruction)
                    ?: throw IllegalStateException("No state for call")
            val refinement = findRefinement(predicate.calledMethod).expanded()
            val withoutCurrentCall = instructionState.filterNot { it == predicate }
            ChainState(withoutCurrentCall, refinement.allStates())
        }
        val expandedState = ChoiceState(listOf(originalState) + exceptionalPaths)
        return CallRefinementsInliner().apply(expandedState).optimize()
    }


    inner class CallRefinementsInliner : RecollectingTransformer<CallRefinementsInliner> {
        override val builders = dequeOf(StateBuilder())
        override fun transformCallPredicate(predicate: CallPredicate): Predicate {
            val refinement = findRefinement(predicate.calledMethod).expanded()
            currentBuilder += refinement.allStates().negateWRTStatePredicates().simplify()
            currentBuilder += BasicState() // fixme: tricky hack to avoid state collapsing
            return predicate
        }
    }

    fun inlineRefinementsV2(state: PredicateState): Pair<PredicateState, RefinementSources> {
        val calls = PredicateCollector.collectIsInstance<CallPredicate>(state).toSet().toList()
        val refinements = calls.map { findRefinement(it.calledMethod) }
        val normalPath = buildNormalPathV2(calls, refinements)
        val exceptionalPaths = buildRefinementSourcesV2(calls, refinements)
        return normalPath to exceptionalPaths
    }

    private fun buildNormalPathV2(calls: List<CallPredicate>, refinements: List<Refinements>): PredicateState {
        val builder = psa.builder(method)
        val result = arrayListOf<PredicateState>()
        val refinementMap = calls.zip(refinements).toMap()
                .mapValues { it.value.allStates() }
        for ((call, _) in zip(calls, refinements)) {
            val state = (builder.getInstructionState(call.instruction) ?: BasicState())
                    .filter { it is CallPredicate || it.type == PredicateType.Path() }
            val refPath = inlineRefinementIntoState(state, refinementMap)
            result.add(refPath)
        }
        return ChoiceState(result).negateWRTStatePredicates()
    }

    private fun buildRefinementSourcesV2(calls: List<CallPredicate>, refinements: List<Refinements>): RefinementSources {
        val builder = psa.builder(method)
        val result = arrayListOf<RefinementSource>()
        val refinementMap = calls.zip(refinements).toMap()
        for ((call, refinement) in zip(calls, refinements)) {
            val otherCalls = refinementMap
                    .filterKeys { it != call }
                    .mapValues { it.value.allStates().negateWRTStatePredicates() }
            val state = (builder.getInstructionState(call.instruction) ?: BasicState())
                    .filter { it is CallPredicate || it.type == PredicateType.Path() }
            for (reft in refinement.expanded().value) {
                val mapping = otherCalls + (call to reft.state)
                val refPath = inlineRefinementIntoState(state, mapping)
                val refSource = RefinementSource.create(reft.criteria, refPath)
                result.add(refSource)
            }
        }
        return RefinementSources.create(result).simplify()
    }

    private fun inlineRefinementIntoState(state: PredicateState, mapping: Map<CallPredicate, PredicateState>): PredicateState =
            MethodFunctionalInliner(psa) {
                val predicateState = mapping[predicate]
                        ?: throw IllegalArgumentException("No method $predicate for inline")
                inline(predicateState)
            }.apply(state)

}

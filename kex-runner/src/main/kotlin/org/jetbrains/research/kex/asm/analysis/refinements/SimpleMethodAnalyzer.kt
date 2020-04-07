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
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kex.util.join
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method

class SimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    private val replacedWithInheritors = hashMapOf<Method, List<Method>>()

    override fun analyze(): Refinements {
        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, method)
        val state = buildMethodState(methodPaths)
        val refinementSources = methodPaths.refinementSources
        val normalPaths = methodPaths.normalExecutionPaths
        val (nestedNormal, nestedRefinementSources) = inlineRefinements()

        val allSources = refinementSources.merge(nestedRefinementSources)
        val allNormal = ChainState(normalPaths, nestedNormal).optimize()

        log.info("Analyze: $method")
        log.info("State:\n$state\nExceptions:\n$allSources\nNormal:\n$allNormal")

        val (trivialRefinements, sourcesToQuery) = searchForDummySolution(allNormal, allSources)
        val otherRefinements = queryRefinementSources(state, allNormal, sourcesToQuery)

        return Refinements(trivialRefinements.value + otherRefinements.value, method)
    }

    override fun findRefinement(method: Method): Refinements {
        if (method !in replacedWithInheritors) return super.findRefinement(method)
        val implementations = replacedWithInheritors[method]!!
        if (implementations.isEmpty()) return super.findRefinement(method)
        val implementationsRefinements = implementations.map { super.findRefinement(it) }
        val owners = implementations.map { buildOwnerTypeChecks(it, method.`class`.kexType) }
        val typeChoices = ChoiceState(owners)
        val implementationChoices = owners.zip(implementationsRefinements).map { (type, state) -> state.fmap { ChainState(type, it) } }
        val mergedRefinement = implementationChoices.join { a, b -> a.merge(b) }
        return mergedRefinement.fmap { ChainState(typeChoices, it) }
    }

    private fun buildMethodState(builder: MethodRefinementSourceAnalyzer): PredicateState {
        val inlinedState = transform(builder.methodRawFullState()) {
            +MethodFunctionalInliner(psa) {
                val state = getStateForInlining()
                when {
                    state != null -> inline(state)
                    state == null && inliningIsPossible() -> {
                        val type = call.owner.type as? KexClass
                        if (type == null || type.kfgClass(cm.type) != calledMethod.`class`) skip()
                        val implementations = replacedWithInheritors[calledMethod]
                                ?: collectImplementations(type, calledMethod).filterNot { it.isEmpty() }
                        if (implementations.isEmpty()) skip()
                        replacedWithInheritors[calledMethod] = implementations
                        val ownerTypes = arrayListOf<PredicateState>()
                        val inliningStates = arrayListOf<PredicateState>()
                        for (implementation in implementations) {
                            val methodState = psa.builder(implementation).methodState ?: continue
                            val ownerType = buildOwnerTypeChecks(implementation, type)
                            ownerTypes.add(ownerType)
                            inliningStates.add(methodState)
                        }
                        val typeChoices = ChoiceState(ownerTypes)
                        val implementationChoices = ChoiceState(ownerTypes.zip(inliningStates).map { (type, state) -> ChainState(type, state) })
                        val resultState = ChainState(typeChoices, implementationChoices)
                        inline(resultState)
                    }
                    else -> skip()
                }
            }
            applyAdapters()
        }
        TypeIndexer.apply(inlinedState)
        return MemorySpacer(inlinedState).apply(inlinedState)
    }

    private fun buildOwnerTypeChecks(method: Method, type: KexType) = basic {
        path {
            tf.getInstanceOf(method.`class`.kexType, tf.getThis(type)) equality const(true)
        }
    }

    private fun collectImplementations(cls: KexClass, method: Method): List<Method> {
        val inheritors = collectInheritors(cls.kfgClass(cm.type)).filterNot { it.isInterface || it.isAbstract }
        return inheritors.map { it.getMethod(method.name, method.desc) }
    }

    private fun collectInheritors(root: Class): Set<Class> {
        val inheritors = hashSetOf(root)
        val queue = dequeOf(root)
        while (queue.isNotEmpty()) {
            val cls = queue.removeFirst()
            val clsInheritors = cm.concreteClasses.filter { it != cls && it.isInheritorOf(cls) }
            inheritors.addAll(clsInheritors)
            queue.addAll(clsInheritors)
        }
        return inheritors
    }

    private fun searchForDummySolution(normal: PredicateState, exceptions: RefinementSources): Pair<Refinements, RefinementSources> {
        val sourcesToQuery = mutableListOf<RefinementSource>()
        val dummyRefinements = mutableListOf<Refinement>()
        for (source in exceptions.value) {
            val dummyResult = analyzeForDummyResult(normal, source.condition)
            if (dummyResult == null) {
                sourcesToQuery.add(source)
                continue
            }
            dummyRefinements.add(Refinement.create(source.criteria, dummyResult))
        }
        return Refinements(dummyRefinements, method) to RefinementSources(sourcesToQuery)
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

    private fun queryRefinementSources(state: PredicateState, normal: PredicateState, sources: RefinementSources): Refinements {
        if (sources.value.isEmpty()) return Refinements(emptyList(), method)
        val conditions = sources.value.map { it.condition }
        val fixpointAnswer = queryFixpointSolver(state, normal, conditions)
        val refinements = sources.value.zip(fixpointAnswer).map { (src, answer) -> Refinement.create(src.criteria, answer) }
        return Refinements(refinements, method)
    }

    private fun queryFixpointSolver(state: PredicateState, normal: PredicateState, exceptions: List<PredicateState>): List<PredicateState> =
            try {
                val result = Z3FixpointSolver(cm.type).mkFixpointQuery(state, exceptions, normal)
                when (result) {
                    is FixpointResult.Sat -> result.result
                    else -> {
                        if (result is FixpointResult.Unknown) log.error("Unknown: ${result.reason}")
                        exceptions.map { falseState() }
                    }
                }
            } catch (ex: QueryCheckStatus.FixpointQueryException) {
                log.error("Bad fixpoint query: ${ex.status}")
                exceptions.map { falseState() }
            }
}
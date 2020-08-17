package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.analysis.refinements.solver.CallResolvingRefinementSourcesAnalyzer
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersioner
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import ru.spbstu.ktuples.zip

class NoInliningSimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    override fun analyze(): Refinements {
        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, method)
        val refinementSources = methodPaths.refinementSources
        val normalPaths = methodPaths.normalExecutionPaths

        val state = extendWithRefinements(methodPaths)
        val (nestedNormal, nestedRefinementSources) = nestedExecutionPaths(state)

        val allSources = refinementSources.merge(nestedRefinementSources).fmap { it.optimize() }
        val allNormal = ChainState(normalPaths, nestedNormal).optimize()

        log.info("Analyze: $method")
        log.debug("State:\n$state\nExceptions:\n$allSources\nNormal:\n$allNormal")

        return CallResolvingRefinementSourcesAnalyzer(this).analyze(state, allNormal, allSources)
    }

    override fun MethodFunctionalInliner.TransformationState.getMethodStateAndRefinement(): Pair<Refinements, PredicateState> {
        throw IllegalStateException("Unavailable")
    }

    inner class CallRefinementsInliner : RecollectingTransformer<CallRefinementsInliner> {
        override val builders = dequeOf(StateBuilder())
        override fun transformCallPredicate(predicate: CallPredicate): Predicate {
            val refinement = callRefinement(predicate)
            currentBuilder += refinement.allStates().negateWRTStatePredicates().simplify()
            currentBuilder += BasicState() // fixme: tricky hack to avoid state collapsing
            return predicate
        }
    }

    private fun callRefinement(predicate: CallPredicate): Refinements =
            findRefinement(predicate.calledMethod)
                    .expanded()
                    .fmap { inlineRefinementIntoState(predicate.wrap(), mapOf(predicate to it)) }

    private fun extendWithRefinements(builder: MethodRefinementSourceAnalyzer): PredicateState {
        val originalState = transform(builder.methodRawFullState()) {
            +ConstructorDeepInliner(psa)
            +SimpleMethodInliner(psa)
        }
        val calls = PredicateCollector.collectIsInstance<CallPredicate>(originalState)
        val exceptionalPaths = calls.map { predicate ->
            val instructionState = psa.builder(method).getInstructionState(predicate.instruction)
                    ?: throw IllegalStateException("No state for call")
            val refinement = callRefinement(predicate)
            val withoutCurrentCall = instructionState.filterNot { it == predicate }
            ChainState(withoutCurrentCall, refinement.allStates())
        }
        val expandedState = ChoiceState(listOf(originalState) + exceptionalPaths)
        val result = transform(expandedState) {
            +CallRefinementsInliner()
            +MemoryVersioner()
        }.optimize()
        MemoryUtils.verifyVersions(result)
        return result
    }

    private fun nestedExecutionPaths(state: PredicateState): Pair<PredicateState, RefinementSources> {
        val calls = PredicateCollector.collectIsInstance<CallPredicate>(state).distinct()
        val refinements = calls.map { findRefinement(it.calledMethod) }
        val normalPath = buildNormalPath(calls, refinements)
        val exceptionalPaths = buildRefinementSources(calls, refinements)
        return normalPath to exceptionalPaths
    }

    private fun buildNormalPath(calls: List<CallPredicate>, refinements: List<Refinements>): PredicateState {
        val inlined = zip(calls, refinements)
                .map { (call, ref) -> inlineRefinementIntoState(call.wrap(), mapOf(call to ref.allStates())) }
        return ChoiceState(inlined).negateWRTStatePredicates()
    }

    private fun buildRefinementSources(calls: List<CallPredicate>, refinements: List<Refinements>): RefinementSources {
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

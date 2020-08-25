package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.analysis.refinements.solver.CallResolvingRefinementSourcesAnalyzer
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.memory.MemoryVersioner
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.MethodFunctionalInliner
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kex.state.transformer.transform
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method

class NoInliningSimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    override fun analyze(): Refinements {
        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, method)
        val inliner = CallInliner(method, psa, this)
        val statePrepared = inliner.apply(methodPaths.methodRawFullState())
        val state = transform(statePrepared) {
            +MemoryVersioner()
        }.optimize()
        val (nestedNormal, nestedSources) = buildRefinementSources(inliner.callPathConditions)
        val allSources = methodPaths.refinementSources.merge(nestedSources).fmap { it.optimize() }
        val allNormal = ChainState(methodPaths.normalExecutionPaths, nestedNormal).optimize()

        log.info("Analyze: $method")
        log.debug("State:\n$state\nExceptions:\n$allSources\nNormal:\n$allNormal")

        return CallResolvingRefinementSourcesAnalyzer(this).analyze(state, allNormal, allSources)
    }

    override fun MethodFunctionalInliner.TransformationState.getMethodStateAndRefinement(): Pair<Refinements, PredicateState> {
        throw IllegalStateException("Unavailable")
    }

    private fun buildRefinementSources(callPathConditions: Map<CallPredicate, PathConditions>): Pair<PredicateState, RefinementSources> {
        val refinementSources = callPathConditions
                .filter { it.value.pc.isNotEmpty() }
                .map { (call, refinements) ->
                    buildRefinementSources(call, refinements, callPathConditions)
                }
                .fold(RefinementSources.empty()) { res, source -> res.merge(source) }
        val normalExecution = callPathConditions.values.map { it.noErrorCondition() }
                .fold(emptyState()) { res, condition -> ChainState(res, condition) }
        return normalExecution to refinementSources
    }

    private fun buildRefinementSources(
            predicate: CallPredicate,
            refinements: PathConditions,
            callPathConditions: Map<CallPredicate, PathConditions>
    ): RefinementSources {
        val state = psa.builder(method).getInstructionState(predicate.instruction)
                ?: error("No state for instruction which is in state")
        val pathConditions = state.filter { it.type == PredicateType.Path() || it is CallPredicate && it != predicate }
        val pathConditionsWithCallsResolved = CallNormalExecutionConditionInliner(callPathConditions).apply(pathConditions)
        val refinementSources = refinements.expandedErrorConditions()
        val refinementSourcesWithFullPath = refinementSources.mapValues { (_, path) -> ChainState(pathConditionsWithCallsResolved, path) }
        val sources = refinementSourcesWithFullPath.map { (criteria, path) -> RefinementSource.create(criteria, path) }
        return RefinementSources.create(sources)
    }

    private class CallNormalExecutionConditionInliner(val callPathConditions: Map<CallPredicate, PathConditions>) : RecollectingTransformer<CallNormalExecutionConditionInliner> {
        override val builders = dequeOf(StateBuilder())
        override fun transformCallPredicate(predicate: CallPredicate): Predicate {
            val conditions = callPathConditions[predicate] ?: return nothing()
            currentBuilder += conditions.noErrorCondition()
            return nothing()
        }

        override fun apply(ps: PredicateState): PredicateState {
            builders.clear()
            builders += StateBuilder()
            return super.apply(ps)
        }
    }

}

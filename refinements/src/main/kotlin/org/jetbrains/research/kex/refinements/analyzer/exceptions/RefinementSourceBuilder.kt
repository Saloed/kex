package org.jetbrains.research.kex.refinements.analyzer.exceptions

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.refinements.RefinementCriteria
import org.jetbrains.research.kex.refinements.RefinementSource
import org.jetbrains.research.kex.refinements.RefinementSources
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.IntrinsicAdapter
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import org.jetbrains.research.kfg.ir.value.instruction.ReturnInst

class RefinementSourceBuilder(
    val method: Method,
    val sources: List<ExceptionSource>,
    private val optimize: Boolean = true
) {
    private val stateBuilder = PredicateStateBuilderWithThrows.forMethod(method)
    private val sourceByInstruction = sources.associateBy { it.instruction }

    fun buildExceptionSources(): RefinementSources {
        val nonEmptySources = sources.filterNot { it.criteria().isEmpty() }
        if (nonEmptySources.isEmpty()) return RefinementSources.empty()
        val refinementSources = nonEmptySources.map { buildExceptionPathsForSource(it) }
                .fold(RefinementSources.empty()) { res, source -> res.merge(source) }
        return refinementSources.fmap { it.optimizeIfEnabled() }
    }

    fun buildNormals(returns: List<ReturnInst>): PredicateState {
        val normalExecutionPaths = when (returns.size) {
            0 -> normalsForNoReturns()
            1 -> normalsForSingleReturn(returns.first())
            else -> error("Too many return instructions")
        }
        return normalExecutionPaths.optimizeIfEnabled()
    }

    private fun PredicateState.optimizeIfEnabled() = when {
        optimize -> optimize()
        else -> this
    }

    private fun normalsForNoReturns(): PredicateState {
        val noExceptionsConditions = sources.filterNot { it.criteria().isEmpty() }
                .map { buildNormalPathForSource(it) }
        return chain(noExceptionsConditions)
    }

    private fun normalsForSingleReturn(returnInst: ReturnInst): PredicateState {
        val stateForInstruction = stateForSource(returnInst)
        val inliner = ExecutionConditionInliner(null, null)
        return inliner.apply(stateForInstruction)
    }

    private fun buildNormalPathForSource(source: ExceptionSource): PredicateState {
        val state = stateForSource(source.instruction)
        val inliner = ExecutionConditionInliner(source, null)
        return inliner.apply(state)
    }

    private fun buildExceptionPathsForSource(source: ExceptionSource): RefinementSources {
        val state = stateForSource(source.instruction)
        val refinementSources = source.criteria().map { criteria ->
            val inliner = ExecutionConditionInliner(source, criteria)
            val executionPath = inliner.apply(state)
            RefinementSource.create(criteria, executionPath)
        }
        return RefinementSources.create(refinementSources)
    }

    private fun stateForSource(instruction: Instruction): PredicateState {
        val executionPath = rawStateForInstruction(instruction)
        val withUnlistedExecutionPaths = notListedExecutionPaths(executionPath, instruction)
        return when (withUnlistedExecutionPaths.size) {
            1 -> executionPath
            else -> ChoiceState(withUnlistedExecutionPaths)
        }
    }

    private fun notListedExecutionPaths(originalState: PredicateState, originalInstruction: Instruction): List<PredicateState> {
        val instructionsExecutedBeforeException = stateBuilder.blocksBeforeInstruction(originalInstruction)
                .flatten()
                .mapIndexed { index, inst -> inst to index }
                .toMap()
        val unlistedInstructions = sourceByInstruction.keys
                .filter { it in instructionsExecutedBeforeException }
                .toMutableSet()

        val states = arrayListOf(originalState)
        unlistedInstructions -= originalState.coveredInstructions()
        while (unlistedInstructions.isNotEmpty()) {
            val unlistedInstruction = unlistedInstructions
                    .maxByOrNull { instructionsExecutedBeforeException.getValue(it) }
                    ?: error("No index for instruction")
            val sourceExecutionPath = rawStateForInstruction(unlistedInstruction)
            states += sourceExecutionPath
            unlistedInstructions -= sourceExecutionPath.coveredInstructions()
        }
        return states
    }

    private fun rawStateForInstruction(instruction: Instruction): PredicateState {
        val state = stateBuilder.getInstructionState(instruction)
                ?.let { IntrinsicAdapter.wrap().apply(it) }
                ?: error("No state for source: $instruction")
        return state.filter { it.mayAffectSourcePath() }
    }

    private fun PredicateState.coveredInstructions(): List<Instruction> = when (this) {
        is BasicState -> coveredInstructions()
        is ChainState -> coveredInstructions()
        is ChoiceState -> coveredInstructions()
        is NegationState -> coveredInstructions()
        else -> error("Unsupported predicate state $this")
    }

    private fun BasicState.coveredInstructions() = predicates.mapNotNull { it.instruction }
    private fun ChainState.coveredInstructions() = base.coveredInstructions() + curr.coveredInstructions()
    private fun ChoiceState.coveredInstructions() = choices.flatMap { it.coveredInstructions() }
    private fun NegationState.coveredInstructions() = predicateState.coveredInstructions()

    private fun Predicate.mayAffectSourcePath(): Boolean {
        if (type == PredicateType.Path()) return true
        if (this is ThrowPredicate) return true
        if (this is CallPredicate) return true
        return false
    }

    private val Predicate.instruction: Instruction?
        get() = when (this) {
            is ThrowPredicate -> inst
            is CallPredicate -> callTerm.instruction
            else -> null
        }

    private inner class ExecutionConditionInliner(
            val targetSource: ExceptionSource?,
            val targetCriteria: RefinementCriteria?
    ) : RecollectingTransformer<ExecutionConditionInliner> {
        override val builders = dequeOf(StateBuilder())
        override fun transformBase(predicate: Predicate): Predicate {
            val resultPredicate = predicate.instruction?.let {
                inlineExceptionSource(sourceByInstruction.getValue(it))
            } ?: predicate
            if (resultPredicate != nothing()) {
                currentBuilder += resultPredicate
            }
            return resultPredicate
        }

        override fun apply(ps: PredicateState): PredicateState {
            builders.clear()
            builders += StateBuilder()
            return super.apply(ps)
        }

        private fun inlineExceptionSource(source: ExceptionSource): Predicate {
            if (source != targetSource || targetCriteria == null) {
                currentBuilder += source.path.noErrorCondition()
                return nothing()
            }
            currentBuilder += source.path.expandedErrorCondition(targetCriteria)
            return nothing()
        }
    }

    private class TransformerWrapper(val transformer: Transformer<*>) : Transformer<TransformerWrapper> {
        override fun transformBase(predicate: Predicate): Predicate {
            if (predicate is ThrowPredicate) return predicate
            return transformer.transformBase(predicate)
        }
    }

    private fun Transformer<*>.wrap() = TransformerWrapper(this)
}

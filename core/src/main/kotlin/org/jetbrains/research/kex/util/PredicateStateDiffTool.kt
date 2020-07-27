package org.jetbrains.research.kex.util

import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.Predicate

@Suppress("unused")
class PredicateStateDiffTool(first: PredicateState, second: PredicateState) : DiffTool<PredicateState>(first, second) {
    override fun diff(parent: DiffNode<PredicateState>?, selector: DiffSelector<PredicateState>?, first: PredicateState, second: PredicateState): DiffNode<PredicateState> {
        if (first == second) return DiffNode.Same(parent, selector)
        if (first::class != second::class) return DiffNode.Different(parent, selector)
        return when (first) {
            is BasicState -> psDiff(DiffNode.Different(parent, selector), first, second as BasicState)
            is NegationState -> psDiff(DiffNode.Different(parent, selector), first, second as NegationState)
            is ChainState -> psDiff(DiffNode.Different(parent, selector), first, second as ChainState)
            is ChoiceState -> psDiff(DiffNode.Different(parent, selector), first, second as ChoiceState)
            is CallApproximationState -> psDiff(DiffNode.Different(parent, selector), first, second as CallApproximationState)
            else -> throw IllegalStateException("Unexpected PS: $first")
        }
    }

    private fun psDiff(node: DiffNode<PredicateState>, first: BasicState, second: BasicState): DiffNode<PredicateState> = node
    private fun psDiff(node: DiffNode<PredicateState>, first: NegationState, second: NegationState): DiffNode<PredicateState> {
        val selector = NegationSelector()
        node.children += diff(node, selector, selector.get(first), selector.get(second))
        return node
    }

    private fun psDiff(node: DiffNode<PredicateState>, first: ChainState, second: ChainState): DiffNode<PredicateState> {
        val baseSelector = ChainSelector(ChainType.BASE)
        val currSelector = ChainSelector(ChainType.CURR)
        node.children += diff(node, baseSelector, baseSelector.get(first), baseSelector.get(second))
        node.children += diff(node, currSelector, currSelector.get(first), currSelector.get(second))
        return node
    }

    private fun psDiff(node: DiffNode<PredicateState>, first: ChoiceState, second: ChoiceState): DiffNode<PredicateState> {
        if (first.choices.size != second.choices.size) return node
        node.children += first.choices.indices.map { idx ->
            val selector = ChoiceSelector(idx)
            diff(node, selector, selector.get(first), selector.get(second))
        }
        return node
    }

    private fun psDiff(node: DiffNode.Different<PredicateState>, first: CallApproximationState, second: CallApproximationState): DiffNode<PredicateState> {
        if (first.call != second.call) return node
        if (first.preconditions.size != second.preconditions.size) return node
        val defaultPre = CallApproximationSelector(null, CallApproximationType.PRE)
        val defaultPost = CallApproximationSelector(null, CallApproximationType.POST)
        node.children += diff(node, defaultPre, defaultPre.get(first), defaultPre.get(second))
        node.children += diff(node, defaultPost, defaultPost.get(first), defaultPost.get(second))
        node.children += first.preconditions.indices.map { idx ->
            val selector = CallApproximationSelector(idx, CallApproximationType.PRE)
            diff(node, selector, selector.get(first), selector.get(second))
        }
        node.children += first.postconditions.indices.map { idx ->
            val selector = CallApproximationSelector(idx, CallApproximationType.POST)
            diff(node, selector, selector.get(first), selector.get(second))
        }
        return node
    }

    override fun createDiffPlaceholder(left: PredicateState, right: PredicateState): PredicateState = PredicateStateDiff(left, right)

    companion object {
        fun diff(first: PredicateState, second: PredicateState) = PredicateStateDiffTool(first, second).diff()
    }
}

class PredicateStateDiff(val left: PredicateState, val right: PredicateState) : PredicateState() {
    override val size: Int
        get() = left.size + right.size

    override fun print(): String = buildString {
        appendLine("<[DIFF")
        appendLine("<LEFT> $left")
        appendLine("<RIGHT> $right")
        append(" DIFF]>")
    }

    override fun fmap(transform: (PredicateState) -> PredicateState): PredicateState = throw IllegalStateException("Diff PS is Just for printing")
    override fun reverse(): PredicateState = throw IllegalStateException("Diff PS is Just for printing")
    override fun addPredicate(predicate: Predicate): PredicateState = throw IllegalStateException("Diff PS is Just for printing")
    override fun sliceOn(state: PredicateState): PredicateState? = throw IllegalStateException("Diff PS is Just for printing")
    override fun performSimplify(): PredicateState = throw IllegalStateException("Diff PS is Just for printing")
    override fun checkEvaluationToTrue(): Boolean = throw IllegalStateException("Diff PS is Just for printing")
    override fun checkEvaluationToFalse(): Boolean = throw IllegalStateException("Diff PS is Just for printing")
}

private class ChoiceSelector(val choiceIdx: Int) : DiffSelector<PredicateState> {
    override fun get(expr: PredicateState): PredicateState = (expr as ChoiceState).choices[choiceIdx]
    override fun set(expr: PredicateState, value: PredicateState): PredicateState {
        expr as ChoiceState
        val newChoices = expr.choices.toMutableList()
        newChoices[choiceIdx] = value
        return ChoiceState(newChoices)
    }
}

private enum class ChainType {
    BASE, CURR;
}

private class ChainSelector(private val type: ChainType) : DiffSelector<PredicateState> {
    override fun get(expr: PredicateState): PredicateState = get(expr as ChainState)
    private fun get(expr: ChainState) = when (type) {
        ChainType.CURR -> expr.curr
        ChainType.BASE -> expr.base
    }

    override fun set(expr: PredicateState, value: PredicateState): PredicateState {
        expr as ChainState
        val (base, curr) = when (type) {
            ChainType.CURR -> expr.base to value
            ChainType.BASE -> value to expr.curr
        }
        return ChainState(base, curr)
    }
}

private class NegationSelector : DiffSelector<PredicateState> {
    override fun get(expr: PredicateState): PredicateState = (expr as NegationState).predicateState
    override fun set(expr: PredicateState, value: PredicateState): PredicateState = NegationState(value)
}

private enum class CallApproximationType {
    PRE, POST
}

private class CallApproximationSelector(val idx: Int?, val type: CallApproximationType) : DiffSelector<PredicateState> {
    override fun get(expr: PredicateState): PredicateState {
        expr as CallApproximationState
        return if (idx == null) when (type) {
            CallApproximationType.PRE -> expr.defaultPrecondition
            CallApproximationType.POST -> expr.defaultPostcondition
        } else when (type) {
            CallApproximationType.PRE -> expr.preconditions[idx]
            CallApproximationType.POST -> expr.postconditions[idx]
        }
    }

    override fun set(expr: PredicateState, value: PredicateState): PredicateState {
        expr as CallApproximationState
        return if (idx == null) when (type) {
            CallApproximationType.PRE -> CallApproximationState(expr.preconditions, expr.postconditions, value, expr.defaultPostcondition, expr.call)
            CallApproximationType.POST -> CallApproximationState(expr.preconditions, expr.postconditions, expr.defaultPrecondition, value, expr.call)
        } else when (type) {
            CallApproximationType.PRE -> CallApproximationState(expr.preconditions.toMutableList().apply { set(idx, value) }, expr.postconditions, expr.defaultPrecondition, expr.defaultPostcondition, expr.call)
            CallApproximationType.POST -> CallApproximationState(expr.preconditions, expr.postconditions.toMutableList().apply { set(idx, value) }, expr.defaultPrecondition, expr.defaultPostcondition, expr.call)
        }
    }
}
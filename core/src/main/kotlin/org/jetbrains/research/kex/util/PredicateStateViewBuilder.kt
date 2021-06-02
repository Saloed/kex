package org.jetbrains.research.kex.util

import org.jetbrains.research.kex.state.*

class PredicateStateViewBuilder {
    fun accept(ps: PredicateState): StructuredViewable.Item = build(ps).enter
    fun accept(ps: PredicateStateWithPath): StructuredViewable.Item = build(ps).enter

    private fun build(ps: PredicateState): ViewBuilderState = when (ps) {
        is BasicState -> build(ps)
        is ChainState -> build(ps)
        is ChoiceState -> build(ps)
        is NegationState -> build(ps)
        is CallApproximationState -> build(ps)
        else -> error("Unexpected predicate state: $ps")
    }

    private fun build(ps: BasicState): ViewBuilderState {
        val label = ps.print().replace("\n", "\\l") + "\\l"
        val item = StructuredViewable.Item.Node(label)
        return ViewBuilderState(item, item)
    }

    private fun build(ps: ChainState): ViewBuilderState {
        val base = build(ps.base)
        val curr = build(ps.curr)
        base.exit.addEdge(curr.enter, "chain")
        return ViewBuilderState(base.enter, curr.exit)
    }

    private fun build(ps: ChoiceState): ViewBuilderState {
        val choices = ps.choices.map { build(it) }
        val enterItem = StructuredViewable.Item.Node("choice", StructuredViewable.ItemKind.OPERATION)
        val exitItem = StructuredViewable.Item.Node("choice merge", StructuredViewable.ItemKind.STUB)
        for (choice in choices) {
            enterItem.addEdge(choice.enter)
            choice.exit.addEdge(exitItem)
        }
        return ViewBuilderState(enterItem, exitItem)
    }

    private fun build(ps: NegationState): ViewBuilderState {
        val state = build(ps.predicateState)
        val item = StructuredViewable.Item.Node("negate", StructuredViewable.ItemKind.OPERATION)
        state.exit.addEdge(item)
        return ViewBuilderState(state.enter, item)
    }

    private fun build(ps: CallApproximationState): ViewBuilderState {
        val enterItem = StructuredViewable.Item.Node("call approx", StructuredViewable.ItemKind.STUB)
        val exitItem = StructuredViewable.Item.Node("call approx", StructuredViewable.ItemKind.STUB)
        ps.preconditions.zip(ps.postconditions) { pre, post ->
            buildCallApprox(enterItem, exitItem, build(pre), build(post), "case", "then")
        }
        buildCallApprox(
            enterItem, exitItem, build(ps.callState), build(ps.defaultPostcondition), "default", "then"
        )
        return makeGroup("call approx", enterItem, exitItem)
    }

    private fun buildCallApprox(
        enter: StructuredViewable.Item.Node,
        exit: StructuredViewable.Item.Node,
        pre: ViewBuilderState,
        post: ViewBuilderState,
        preLabel: String,
        postLabel: String
    ) {
        enter.addEdge(pre.enter, preLabel)
        pre.exit.addEdge(post.enter, postLabel)
        post.exit.addEdge(exit)
    }

    private fun build(ps: PredicateStateWithPath): ViewBuilderState {
        val path = build(ps.path)
        val state = build(ps.state)
        val pathGroup = StructuredViewable.Item.ItemGroup("path", path.enter, path.exit)
        val stateGroup = StructuredViewable.Item.ItemGroup("state", state.enter, state.exit)
        val enterNode = StructuredViewable.Item.Node("state with path", StructuredViewable.ItemKind.STUB)
        val exitNode = StructuredViewable.Item.Node("state with path", StructuredViewable.ItemKind.STUB)
        enterNode.addEdge(pathGroup)
        enterNode.addEdge(stateGroup)
        path.exit.addEdge(exitNode)
        state.exit.addEdge(exitNode)
        return makeGroup("state with path", enterNode, exitNode)
    }

    private fun makeGroup(name: String, enter: StructuredViewable.Item, exit: StructuredViewable.Item.Node) =
        ViewBuilderState(StructuredViewable.Item.ItemGroup(name, enter, exit), exit)

    private data class ViewBuilderState(val enter: StructuredViewable.Item, val exit: StructuredViewable.Item.Node)

}
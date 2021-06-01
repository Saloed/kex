package org.jetbrains.research.kex.state

import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.util.StructuredViewable
import org.jetbrains.research.kthelper.defaultHashCode

@InheritorOf("State")
@Serializable
class NegationState(@Required val predicateState: PredicateState) : PredicateState() {

    override val size: Int
        get() = predicateState.size

    override fun print() = buildString {
        appendLine("(NOT")
        appendLine(predicateState.print())
        append(")")
    }

    override val graphItem: StructuredViewable.Item by lazy {
        StructuredViewable.Item.Node("not", StructuredViewable.ItemKind.OPERATION).apply {
            addEdge(predicateState.graphItem)
        }
    }

    override fun map(transform: (Predicate) -> Predicate) = NegationState(predicateState.map(transform))
    override fun fmap(transform: (PredicateState) -> PredicateState) = NegationState(predicateState.fmap(transform))
    override fun mapNotNull(transform: (Predicate) -> Predicate?) = NegationState(predicateState.mapNotNull(transform))
    override fun filter(predicate: (Predicate) -> Boolean) = NegationState(predicateState.filter(predicate))
    override fun reverse(): PredicateState = NegationState(predicateState.reverse())

    override fun hashCode() = defaultHashCode("NOT", predicateState)
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != this.javaClass) return false
        other as NegationState
        return this.predicateState == other.predicateState
    }

    override fun addPredicate(predicate: Predicate) = ChainState(this, BasicState(arrayListOf(predicate)))

    override fun sliceOn(state: PredicateState): PredicateState? {
        val sliced = predicateState.sliceOn(state) ?: return null
        return NegationState(sliced)
    }

    override fun performSimplify(): PredicateState = NegationState(predicateState.simplify())
    override fun checkEvaluationToTrue(): Boolean = predicateState.evaluatesToFalse
    override fun checkEvaluationToFalse(): Boolean = predicateState.evaluatesToTrue
}

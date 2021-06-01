package org.jetbrains.research.kex.state

import org.jetbrains.research.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.util.StructuredViewable

@InheritorOf("State")
@Serializable
class ChoiceState(val choices: List<PredicateState>) : PredicateState(), Iterable<PredicateState> {
    override val size: Int by lazy(LazyThreadSafetyMode.NONE) { choices.fold(0) { acc, it -> acc + it.size } }

    override fun print() = buildString {
        appendLine("(BEGIN")
        append(choices.joinToString { " <OR> $it" })
        append(" END)")
    }

    override val graphItem: StructuredViewable.Item by lazy {
        StructuredViewable.Item.Node("choice", StructuredViewable.ItemKind.OPERATION).apply {
            choices.forEach { addEdge(it.graphItem) }
        }
    }

    override fun fmap(transform: (PredicateState) -> PredicateState): PredicateState = ChoiceState(choices.map { transform(it) })
    override fun reverse() = ChoiceState(choices.map { it.reverse() })

    override fun hashCode() = defaultHashCode(*choices.toTypedArray())

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != this.javaClass) return false
        other as ChoiceState
        return this.choices.toTypedArray().contentEquals(other.choices.toTypedArray())
    }

    override fun addPredicate(predicate: Predicate) = ChainState(ChoiceState(choices), BasicState(arrayListOf(predicate)))

    override fun sliceOn(state: PredicateState): PredicateState? {
        if (this == state) return emptyState()
        val slices = choices.map { it.sliceOn(state) }
        val filtered = slices.filterNotNull()
        return if (slices.size == filtered.size) ChoiceState(filtered) else null
    }

    override fun iterator() = choices.iterator()

    override fun performSimplify(): PredicateState {
        val simplifiedChoices = choices.map { it.simplify() }.distinct()
        return when {
            simplifiedChoices.isEmpty() -> falseState()
            simplifiedChoices.size == 1 -> simplifiedChoices.first()
            simplifiedChoices == choices -> this
            else -> ChoiceState(simplifiedChoices)
        }
    }

    override fun checkEvaluationToTrue(): Boolean = choices.any { it.evaluatesToTrue }
    override fun checkEvaluationToFalse(): Boolean = choices.all { it.evaluatesToFalse }
}

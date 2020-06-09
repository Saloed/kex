package org.jetbrains.research.kex.state

import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.state.predicate.Predicate
import com.abdullin.kthelper.defaultHashCode

@InheritorOf("State")
@Serializable
class NegationState(@Required val predicateState: PredicateState) : PredicateState() {

    override val size: Int
        get() = predicateState.size

    override fun print() = buildString {
        appendln("(")
        appendln("NOT")
        appendln(predicateState.print())
        append(")")
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

    override fun addPredicate(predicate: Predicate) = NegationState(predicateState + predicate)

    override fun sliceOn(state: PredicateState): PredicateState? {
        val sliced = predicateState.sliceOn(state) ?: return null
        return NegationState(sliced)
    }

    override fun simplify(): PredicateState = NegationState(predicateState.simplify())

    override val evaluatesToTrue: Boolean by lazy(LazyThreadSafetyMode.NONE) { predicateState.evaluatesToFalse }
    override val evaluatesToFalse: Boolean by lazy(LazyThreadSafetyMode.NONE) { predicateState.evaluatesToTrue }
}

package org.jetbrains.research.kex.state

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.state.predicate.Predicate

@InheritorOf("State")
@Serializable
class ImpliesState(val base: PredicateState, val curr: PredicateState) : PredicateState() {
    override val size: Int by lazy(LazyThreadSafetyMode.NONE) { base.size + curr.size }

    override fun print() = buildString {
        append(base.print())
        append(" => ")
        append(curr.print())
    }

    override fun fmap(transform: (PredicateState) -> PredicateState) = ImpliesState(transform(base), transform(curr))
    override fun reverse() = ImpliesState(curr.reverse(), base.reverse())

    override fun hashCode() = defaultHashCode(base, curr)
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != this.javaClass) return false
        other as ImpliesState
        return this.base == other.base && this.curr == other.curr
    }

    override fun addPredicate(predicate: Predicate) = TODO()
    override fun sliceOn(state: PredicateState): PredicateState? = TODO()
    override fun performSimplify(): PredicateState {
        val sbase = base.simplify()
        val scurr = curr.simplify()
        return ImpliesState(sbase, scurr)
    }

    override fun checkEvaluationToTrue(): Boolean = base.evaluatesToFalse || curr.evaluatesToTrue
    override fun checkEvaluationToFalse(): Boolean = base.evaluatesToTrue && curr.evaluatesToFalse
}

package org.jetbrains.research.kex.state

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate

@InheritorOf("State")
@Serializable
class CallApproximationState(
        @Required val preconditions: List<PredicateStateWithPath>,
        @Required val postconditions: List<PredicateStateWithPath>,
        @Required val callState: PredicateState,
        @Required val defaultPostcondition: PredicateStateWithPath,
        @Required val call: CallPredicate
) : PredicateState() {
    constructor(
            preconditions: List<PredicateStateWithPath>,
            postconditions: List<PredicateStateWithPath>,
            call: CallPredicate,
            defaultPostcondition: PredicateStateWithPath
    ) : this(preconditions, postconditions, call.wrap(), defaultPostcondition, call)

    init {
        require(preconditions.size == postconditions.size) { "invalid number of pre and post conditions" }
    }

    override val size: Int by lazy(LazyThreadSafetyMode.NONE) {
        preconditions.sumBy { it.size } + postconditions.sumBy { it.size } + defaultPostcondition.size + callState.size
    }

    override fun print() = buildString {
        appendLine("(CALL")
        append(preconditions.zip(postconditions).joinToString { (cond, ps) -> " <CASE> $cond <THEN> $ps" })
        append(" <DEFAULT> $callState <THEN> $defaultPostcondition")
        append(" END)")
    }

    override fun fmap(transform: (PredicateState) -> PredicateState): PredicateState = CallApproximationState(
            preconditions.map { it.accept(transform) },
            postconditions.map { it.accept(transform) },
            transform(callState),
            defaultPostcondition.accept(transform),
            call
    )

    override fun filter(predicate: (Predicate) -> Boolean): PredicateState = emptyState()

    override fun reverse() = TODO()
    override fun hashCode() = defaultHashCode(preconditions, postconditions, call, defaultPostcondition)
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != this.javaClass) return false
        other as CallApproximationState
        return this.preconditions == other.preconditions
                && this.postconditions == other.postconditions
                && this.call == other.call
                && this.defaultPostcondition == other.defaultPostcondition
                && this.callState == other.callState
    }

    override fun addPredicate(predicate: Predicate) = ChainState(this, predicate.wrap())
    override fun sliceOn(state: PredicateState): PredicateState? = TODO()
    override fun performSimplify(): PredicateState = fmap { it.simplify() }

    override fun checkEvaluationToTrue(): Boolean = false   // todo: too complex for now
    override fun checkEvaluationToFalse(): Boolean = false  // todo: too complex for now
}

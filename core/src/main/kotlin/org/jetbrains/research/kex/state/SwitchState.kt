package org.jetbrains.research.kex.state

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.state.predicate.Predicate

@InheritorOf("State")
@Serializable
class SwitchState(val cases: List<Pair<PredicateState, PredicateState>>, val default: PredicateState) : PredicateState() {
    constructor(cases: Map<PredicateState, PredicateState>, default: PredicateState) : this(cases.map { it.key to it.value }, default)

    override val size: Int by lazy(LazyThreadSafetyMode.NONE) {
        cases.fold(0) { acc, (k, v) -> acc + k.size + v.size } + default.size
    }

    override fun print() = buildString {
        appendln("(SWITCH")
        append(cases.joinToString { (cond, ps) -> " <CASE> $cond <THEN> $ps" })
        append(" <DEFAULT> $default")
        append(" END)")
    }

    override fun fmap(transform: (PredicateState) -> PredicateState): PredicateState {
        return SwitchState(transformCases(transform), transform(default))
    }

    fun <T> transformCases(transform: (PredicateState) -> T) = cases.map { (k, v) -> transform(k) to transform(v) }

    override fun reverse() = TODO()
    override fun hashCode() = defaultHashCode(cases, default)
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != this.javaClass) return false
        other as SwitchState
        return this.cases == other.cases && this.default == other.default
    }

    override fun addPredicate(predicate: Predicate) = ChainState(this, predicate.wrap())
    override fun sliceOn(state: PredicateState): PredicateState? = TODO()
    override fun performSimplify(): PredicateState = fmap { it.simplify() }

    override fun checkEvaluationToTrue(): Boolean = false   // todo: too complex for now
    override fun checkEvaluationToFalse(): Boolean = false  // todo: too complex for now
}

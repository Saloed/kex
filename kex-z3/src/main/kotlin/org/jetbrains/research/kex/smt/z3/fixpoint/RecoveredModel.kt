package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.memory.MemoryAccess
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.Term

data class RecoveredModel(val state: PredicateState, val dependencies: Set<TermDependency>) {
    val isFinal: Boolean
        get() = dependencies.isEmpty()

    fun finalStateOrException(): PredicateState = when {
        isFinal -> state
        else -> throw IllegalStateException("State is not final")
    }

    companion object {
        fun error() = RecoveredModel(falseState(), emptySet())
    }
}


sealed class TermDependency {
    abstract val callIdx: Int
    abstract val call: CallPredicate

    data class CallResultDependency(val term: Term, override val callIdx: Int, override val call: CallPredicate) : TermDependency()
    data class MemoryDependency(val memoryAccess: MemoryAccess<*>, override val callIdx: Int, override val call: CallPredicate) : TermDependency()
}
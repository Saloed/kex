package org.jetbrains.research.kex.util

import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.ValueTerm

fun structuralMatch(
    left: PredicateState,
    right: PredicateState,
    varCheck: (ValueTerm, ValueTerm) -> Boolean
): Boolean {
    if (left.javaClass != right.javaClass) return false
    return when (left) {
        is BasicState -> sameCast(left, right).let { (l, r) ->
            all(l.predicates, r.predicates) { a, b -> structuralMatch(a, b, varCheck) }
        }
        is NegationState -> sameCast(left, right).let { (l, r) ->
            structuralMatch(l.predicateState, r.predicateState, varCheck)
        }
        is ChainState -> sameCast(left, right).let { (l, r) ->
            structuralMatch(l.base, r.base, varCheck) && structuralMatch(l.curr, r.curr, varCheck)
        }
        is ChoiceState -> sameCast(left, right).let { (l, r) ->
            all(l.choices, r.choices) { a, b -> structuralMatch(a, b, varCheck) }
        }
        is CallApproximationState -> sameCast(left, right).let { (l, r) ->
            val lhs = listOf(l.defaultPostcondition) + l.postconditions + l.preconditions
            val rhs = listOf(r.defaultPostcondition) + r.postconditions + r.preconditions
            all(lhs, rhs) { a, b -> structuralMatch(a, b, varCheck) }
                    && structuralMatch(l.call, r.call, varCheck)
                    && structuralMatch(l.callState, r.callState, varCheck)
        }
        else -> error("Unexpected PS: $left")
    }
}

private fun structuralMatch(left: Predicate, right: Predicate, varCheck: (ValueTerm, ValueTerm) -> Boolean): Boolean {
    if (left.javaClass != right.javaClass) return false
    if (left.type != right.type || left.location != right.location) return false
    return all(left.operands, right.operands) { l, r -> structuralMatch(l, r, varCheck) }
}

private fun structuralMatch(left: Term, right: Term, varCheck: (ValueTerm, ValueTerm) -> Boolean): Boolean {
    if (left.javaClass != right.javaClass) return false
    if (left.type != right.type) return false
    if (left is ValueTerm) return sameCast(left, right).let { varCheck(it.first, it.second) }
    return all(left.subterms, right.subterms) { l, r -> structuralMatch(l, r, varCheck) }
}

fun structuralMatch(
    left: PredicateStateWithPath,
    right: PredicateStateWithPath,
    varCheck: (ValueTerm, ValueTerm) -> Boolean = { _, _ -> true }
) = structuralMatch(left.state, right.state, varCheck) && structuralMatch(left.path, right.path, varCheck)

private inline fun <reified T> sameCast(left: T, right: Any): Pair<T, T> = left to (right as T)
private inline fun <reified T> all(left: List<T>, right: List<T>, check: (T, T) -> Boolean) = when {
    left.size != right.size -> false
    else -> left.zip(right).all { check(it.first, it.second) }
}

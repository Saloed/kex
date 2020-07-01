package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.state.BasicState
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.path
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.TermBuilder


data class TermWithAxiom(val term: Term, val axiom: PredicateState? = null) {
    fun equality(other: TermWithAxiom): PredicateState {
        val predicate = path { term equality other.term }
        val axiom = mergeAxiom(other)
        return withAxiom(predicate, axiom)
    }

    fun equality(builder: TermBuilder.() -> Term): PredicateState = equality(wrap(builder))

    fun binaryOperation(other: TermWithAxiom, operation: TermBuilder.(Term, Term) -> Term): TermWithAxiom =
            TermWithAxiom(TermBuilder.Terms.operation(term, other.term), mergeAxiom(other))

    fun transformTerm(operation: TermBuilder.(Term) -> Term) = copy(term = TermBuilder.Terms.operation(term))

    private fun withAxiom(predicate: Predicate, axiom: PredicateState?): PredicateState {
        val state = BasicState(listOf(predicate))
        return when {
            axiom != null -> ChainState(axiom, state)
            else -> state
        }
    }

    private fun mergeAxiom(other: TermWithAxiom) = when {
        axiom != null && other.axiom != null -> ChainState(axiom, other.axiom)
        else -> axiom ?: other.axiom
    }

    companion object {
        fun wrap(builder: TermBuilder.() -> Term) = TermWithAxiom(TermBuilder.Terms.builder())
    }
}
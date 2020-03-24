package org.jetbrains.research.kex.state.transformer

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.ValueTerm

class StateReducer : Transformer<StateReducer> {

    class PredicateRemover(val reduceCandidates: Set<Predicate>) : Transformer<PredicateRemover> {
        override fun transformBase(predicate: Predicate) = when {
            predicate in reduceCandidates -> nothing()
            else -> predicate
        }
    }

    private fun collectCandidates(ps: PredicateState): Set<Predicate> {
        val predicateVariables = arrayListOf<Pair<Predicate, Set<Term>>>()
        ps.map { predicate ->
            val variables = VariableCollector().apply { transform(predicate) }.variables
            predicateVariables.add(predicate to variables)
            predicate
        }
        val variableUsages = hashMapOf<Term, List<Predicate>>()
        for ((predicate, vars) in predicateVariables) {
            for (variable in vars) {
                variableUsages[variable] = (variableUsages[variable] ?: emptyList()) + predicate
            }
        }
        return variableUsages
                .filterKeys { it is ValueTerm }
                .filterValues { isReduceCandidate(it) }
                .values
                .flatten()
                .toSet()
    }

    override fun apply(ps: PredicateState): PredicateState {
        var result = ps
        while (true) {
            val candidates = collectCandidates(result)
            if (candidates.isEmpty()) break
            result = PredicateRemover(candidates).apply(result)
        }
        return result
    }

    private fun isReduceCandidate(predicates: List<Predicate>): Boolean {
        val equalities = predicates.filterIsInstance<EqualityPredicate>()
        if (predicates.size != equalities.size) return false
        if (equalities.isEmpty()) throw IllegalStateException("Empty candidate list")
        if (equalities.size == 1) return true
        val first = equalities.first()
        return equalities.all { it == first }
    }

}

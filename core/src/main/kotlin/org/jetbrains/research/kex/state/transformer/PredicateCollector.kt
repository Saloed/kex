package org.jetbrains.research.kex.state.transformer

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.Predicate

class PredicateCollector(val filter: (Predicate) -> Boolean) : Transformer<PredicateCollector> {
    val predicates = mutableListOf<Predicate>()
    override fun transformPredicate(predicate: Predicate): Predicate {
        if (filter(predicate)) predicates.add(predicate)
        return super.transformPredicate(predicate)
    }

    companion object {
        inline fun <reified T : Predicate> collectIsInstance(ps: PredicateState): List<T> {
            val collector = PredicateCollector { it is T }
            collector.transform(ps)
            return collector.predicates.filterIsInstance<T>()
        }
    }
}

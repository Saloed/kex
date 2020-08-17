package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer

interface MemoryVersionTransformer : Transformer<MemoryVersionTransformer> {
    fun <T> transformMemoryVersion(element: MemoryAccess<T>): T = element.withMemoryVersion(element.memoryVersion)

    @Suppress("UNCHECKED_CAST")
    override fun transformTerm(term: Term): Term = when (term) {
        is MemoryAccess<*> -> transformMemoryVersion(term as MemoryAccess<Term>)
        else -> term
    }

    @Suppress("UNCHECKED_CAST")
    override fun transformPredicate(predicate: Predicate): Predicate = when (predicate) {
        is MemoryAccess<*> -> transformMemoryVersion(predicate as MemoryAccess<Predicate>)
        else -> predicate
    }
}
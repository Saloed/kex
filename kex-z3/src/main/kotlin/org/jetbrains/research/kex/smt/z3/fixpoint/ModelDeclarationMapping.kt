package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.collectArguments

class ModelDeclarationMapping(val declarations: List<DeclarationTracker.Declaration>) {
    private val terms = declarations.map { null }.toMutableList<Term?>()

    fun initializeTerms(ps: PredicateState) {
        val (thisArg, otherArgs) = collectArguments(ps)
        for ((index, declaration) in declarations.withIndex()) {
            if (declaration !is DeclarationTracker.Declaration.Argument) continue
            val term = otherArgs.values.find { it.index == declaration.index }
                    ?: throw IllegalStateException("Argument $declaration not found ")
            terms[index] = term
        }
    }

    fun setTerm(declaration: DeclarationTracker.Declaration, term: Term) {
        val idx = declarations.indexOf(declaration)
        if (idx == -1) throw IllegalArgumentException("Unknown declaration: $declaration")
        terms[idx] = term
    }

    fun getTerm(idx: Int): Term = terms[idx]
            ?: throw IllegalArgumentException("No term for declaration $idx: ${declarations[idx]}")

    companion object {
        fun create(declarations: List<DeclarationTracker.Declaration>, ps: PredicateState): ModelDeclarationMapping {
            val mapping = ModelDeclarationMapping(declarations)
            mapping.initializeTerms(ps)
            return mapping
        }
    }
}

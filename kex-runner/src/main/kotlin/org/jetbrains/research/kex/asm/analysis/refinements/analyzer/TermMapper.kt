package org.jetbrains.research.kex.asm.analysis.refinements.analyzer

import org.jetbrains.research.kex.state.term.ArgumentTerm
import org.jetbrains.research.kex.state.term.ReturnValueTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.ValueTerm
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.util.VariableGenerator

open class TermMapper(
        private val variableGenerator: VariableGenerator,
        private val mapping: Map<Term, Term>,
        private val specialCaseMapper: (TermMapper.(Term) -> Term?)? = null
) : Transformer<TermMapper> {
    override fun transformTerm(term: Term): Term = mapping[term] ?: when (term) {
        is ValueTerm, is ArgumentTerm, is ReturnValueTerm -> specialCaseMapper?.invoke(this, term)
                ?: variableGenerator.generatorFor(term).createVar(term.type)
        else -> term
    }
}

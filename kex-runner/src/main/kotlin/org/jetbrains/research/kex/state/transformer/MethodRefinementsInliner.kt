package org.jetbrains.research.kex.state.transformer

import org.jetbrains.research.kex.asm.analysis.MethodRefinementsManager
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.*
import java.util.*

class MethodRefinementsInliner(
        private val refinements: MethodRefinementsManager
) : RecollectingTransformer<MethodRefinementsInliner> {
    private val im = MethodManager.InlineManager
    override val builders = ArrayDeque<StateBuilder>()
    private var inlineIndex = 0

    init {
        builders.push(StateBuilder())
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val calledMethod = (predicate.call as CallTerm).method
        val refinement = refinements.gerOrComputeRefinement(calledMethod)
        val mappings = im.methodArguments(predicate)
        currentBuilder += TermRenamerWithRefinements("inlined_refinement${inlineIndex++}", mappings).apply(refinement)
        return nothing()
    }
}

private class TermRenamerWithRefinements(val suffix: String, val remapping: Map<Term, Term>) : Transformer<TermRenamerWithRefinements> {
    override fun transformTerm(term: Term): Term = remapping[term] ?: when (term) {
        is ValueTerm, is ArgumentTerm, is ReturnValueTerm -> term { value(term.type, "${term.name}.$suffix") }
        else -> term
    }
}

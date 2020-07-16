package org.jetbrains.research.kex.state.transformer

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kfg.ir.Method

open class MethodInliner(val psa: PredicateStateAnalysis) : RecollectingTransformer<MethodInliner> {
    private val im = MethodManager.InlineManager
    override val builders = dequeOf(StateBuilder())
    private var inlineIndex = 0

    class TermRenamer(val suffix: String, val remapping: Map<Term, Term>) : Transformer<TermRenamer> {
        override fun transformTerm(term: Term): Term = remapping[term] ?: when (term) {
            is ValueTerm, is ArgumentTerm, is ReturnValueTerm -> term { value(term.type, "${term.name}.$suffix") }
            else -> term
        }
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val call = predicate.call as CallTerm
        val calledMethod = call.method
        if (!im.isInlinable(calledMethod).toBool()) return predicate

        val mappings = im.methodArguments(predicate)

        currentBuilder += prepareInlinedState(predicate, calledMethod, mappings) ?: return predicate

        return nothing()
    }

    open fun methodState(method: Method): PredicateState? = psa.builder(method).methodState

    open fun prepareInlinedState(call: CallPredicate, method: Method, mappings: Map<Term, Term>): PredicateState? {
        if (method.isEmpty()) return null
        val endState = methodState(method) ?: return null
        return renameTermsAfterInlining(call, endState, mappings)
    }

    open fun renameTermsAfterInlining(call: CallPredicate, state: PredicateState, mappings: Map<Term, Term>): PredicateState {
        return TermRenamer("inlined${inlineIndex++}", mappings).apply(state)
    }
}
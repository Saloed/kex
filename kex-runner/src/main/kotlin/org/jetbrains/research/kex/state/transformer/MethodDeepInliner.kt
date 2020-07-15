package org.jetbrains.research.kex.state.transformer

import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kfg.ir.Method

abstract class MethodDeepInliner(psa: PredicateStateAnalysis, val inlineIf: (CallPredicate) -> Boolean) : MethodInliner(psa) {
    override fun prepareInlinedState(call: CallPredicate, method: Method, mappings: Map<Term, Term>): PredicateState? {
        val preparedState = super.prepareInlinedState(call, method, mappings) ?: return null
        return create().apply(preparedState)
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate = when (inlineIf(predicate)) {
        true -> super.transformCallPredicate(predicate)
        false -> predicate
    }

    abstract fun create(): MethodDeepInliner
}

class ConstructorDeepInliner(psa: PredicateStateAnalysis) : MethodDeepInliner(psa, { (it.call as CallTerm).method.isConstructor }) {
    override fun prepareInlinedState(call: CallPredicate, method: Method, mappings: Map<Term, Term>): PredicateState? {
        if (method.isEmpty() && isObjectConstructor(method)) return emptyState()
        return super.prepareInlinedState(call, method, mappings)
    }

    override fun create(): MethodDeepInliner = ConstructorDeepInliner(psa)

    private fun isObjectConstructor(method: Method): Boolean {
        if (!method.isConstructor) return false
        val clsName = method.`class`.fullname
        return clsName == JAVA_OBJECT || clsName == KOTLIN_ANY
    }

    companion object {
        private const val KOTLIN_ANY = "kotlin/Any"
        private const val JAVA_OBJECT = "java/lang/Object"
    }
}
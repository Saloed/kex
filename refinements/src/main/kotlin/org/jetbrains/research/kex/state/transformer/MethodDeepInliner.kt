package org.jetbrains.research.kex.state.transformer

import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.Class
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
        return isJavaInlineable(method.klass) || isKotlinInlineable(method.klass)
    }

    private fun isKotlinInlineable(cls: Class): Boolean {
        if (cls.pkg != KOTLIN_PACKAGE) return false
        if (cls.name == "Any") return true
        return false
    }

    private fun isJavaInlineable(cls: Class): Boolean {
        if (cls.pkg != JAVA_PACKAGE) return false
        if (cls.name == "Object") return true
        if (cls.name.endsWith("Exception")) return true
        return false
    }

    companion object {
        private val JAVA_PACKAGE = Package.parse("java/lang")
        private val KOTLIN_PACKAGE = Package.parse("kotlin")
    }
}


class SimpleMethodInliner(psa: PredicateStateAnalysis) : MethodDeepInliner(psa, { isSimpleInlinable(psa, it) }) {
    override fun create(): MethodDeepInliner = SimpleMethodInliner(psa)

    companion object {
        private fun isSimpleInlinable(psa: PredicateStateAnalysis, callPredicate: CallPredicate): Boolean {
            val method = (callPredicate.call as CallTerm).method
            val inlineStatus = MethodManager.InlineManager.isInlinable(method)
            if (inlineStatus != MethodManager.InlineManager.InlineStatus.INLINE) return false
            if (method.isEmpty()) return false
            val state = psa.builder(method).methodState ?: return false
            val nestedCalls = PredicateCollector.collectIsInstance<CallPredicate>(state)
            if (nestedCalls.isNotEmpty()) return false
            return true
        }
    }
}
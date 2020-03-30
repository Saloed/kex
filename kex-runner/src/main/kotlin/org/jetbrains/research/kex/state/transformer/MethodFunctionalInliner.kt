package org.jetbrains.research.kex.state.transformer

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.BasicState
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kfg.ir.Method

class MethodFunctionalInliner(
        private val psa: PredicateStateAnalysis,
        private val transformation: TransformationState.() -> Unit
) : RecollectingTransformer<MethodFunctionalInliner> {
    override val builders = dequeOf(StateBuilder())
    private val im = MethodManager.InlineManager
    private var inlineIndex = 0

    inner class TransformationState(val predicate: CallPredicate) {
        val calledMethod: Method = (predicate.call as CallTerm).method
        var currentResult: Predicate = nothing()

        fun getStateForInlining(): PredicateState? {
            if (!im.isInlinable(calledMethod)) return null
            if (calledMethod.isEmpty()) return null
            val builder = psa.builder(calledMethod)
            return builder.methodState
        }

        fun fixPathPredicatesOnTopLevelBeforeInlining(ps: PredicateState): PredicateState = PathPredicatesOnTopLevelBeforeInliningFixer(predicate).apply(ps)

        fun prepareForInline(body: PredicateState): PredicateState {
            val mappings = im.methodArguments(predicate)
            return TermRenamer("inlined_var_${inlineIndex++}", mappings).apply(body)
        }

        fun inline(body: PredicateState) {
            currentBuilder += prepareForInline(body)
        }

        fun skip(): Nothing {
            currentResult = predicate
            throw StopInliningException()
        }
    }

    private class StopInliningException : Exception() {
        override fun fillInStackTrace(): Throwable = this
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val state = TransformationState(predicate)
        try {
            state.transformation()
        } catch (ex: StopInliningException) {
        }
        return state.currentResult
    }

    private class TermRenamer(val suffix: String, val remapping: Map<Term, Term>) : Transformer<TermRenamer> {
        override fun transformTerm(term: Term): Term = remapping[term] ?: when (term) {
            is ValueTerm, is ArgumentTerm, is ReturnValueTerm -> term { value(term.type, "${term.name}.$suffix") }
            else -> term
        }
    }
}

private class PathPredicatesOnTopLevelBeforeInliningFixer(val call: Predicate) : Transformer<PathPredicatesOnTopLevelBeforeInliningFixer> {
    private lateinit var appliedTo: PredicateState
    override fun transformChoice(ps: ChoiceState): PredicateState = ps
    override fun transformBasic(ps: BasicState): PredicateState {
        if (ps.predicates.all { it.type != PredicateType.Path() }) return ps
        log.warn("Path predicates on top level when inlining $call:\n$appliedTo")
        return BasicState(ps.predicates.filter { it.type != PredicateType.Path() })
    }

    override fun apply(ps: PredicateState): PredicateState {
        appliedTo = ps
        return super.apply(ps)
    }
}

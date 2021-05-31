package org.jetbrains.research.kex.state.transformer

import org.jetbrains.research.kthelper.collection.dequeOf
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.KexPointer
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.state.BasicState
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.type.ClassType

class MethodFunctionalInliner(
        private val psa: PredicateStateAnalysis,
        private val transformation: TransformationState.() -> Unit
) : RecollectingTransformer<MethodFunctionalInliner> {
    override val builders = dequeOf(StateBuilder())
    private val im = MethodManager.InlineManager
    private var inlineIndex = 0

    private val knownTransformations = hashMapOf<Predicate, TransformationResult>()

    sealed class TransformationResult {
        object Skip : TransformationResult()
        data class Action(val inlinedState: List<PredicateState>) : TransformationResult()

        fun inline(state: PredicateState): TransformationResult = when (this) {
            is Skip -> Action(listOf(state))
            is Action -> Action(this.inlinedState + listOf(state))
        }
    }

    inner class TransformationState(val predicate: CallPredicate) {
        val call: CallTerm = predicate.call as CallTerm
        val calledMethod: Method = call.method
        var transformationResult: TransformationResult = TransformationResult.Skip

        fun getStateForInlining(): PredicateState? = when (im.isInlinable(calledMethod)) {
            MethodManager.InlineManager.InlineStatus.NO_INLINE -> null
            MethodManager.InlineManager.InlineStatus.MAY_INLINE -> null
            MethodManager.InlineManager.InlineStatus.INLINE -> when {
                calledMethod.isEmpty() -> null
                else -> psa.builder(calledMethod).methodState
            }
        }

        fun inliningIsPossible() = when (im.isInlinable(calledMethod)) {
            MethodManager.InlineManager.InlineStatus.INLINE -> true
            MethodManager.InlineManager.InlineStatus.MAY_INLINE -> true
            MethodManager.InlineManager.InlineStatus.NO_INLINE -> false
        }

        fun fixPathPredicatesOnTopLevelBeforeInlining(ps: PredicateState): PredicateState = PathPredicatesOnTopLevelBeforeInliningFixer(predicate).apply(ps)

        fun prepareForInline(body: PredicateState): PredicateState {
            val withoutIntrinsics = IntrinsicAdapter.apply(body)
            val noMemspace = MemorySpaceRemover.apply(withoutIntrinsics)
            val mappings = methodArguments(predicate)
            return TermRenamer("inlined${inlineIndex++}", mappings).apply(noMemspace)
        }

        fun inline(body: PredicateState) {
            val stateForInline = prepareForInline(body)
            transformationResult = transformationResult.inline(stateForInline)
        }

        fun skip(): Nothing {
            throw StopInliningException()
        }
    }

    private class StopInliningException : Exception() {
        override fun fillInStackTrace(): Throwable = this
    }

    override fun transformCallPredicate(predicate: CallPredicate): Predicate = knownTransformations
            .getOrPut(predicate, { createTransformation(predicate) })
            .applyTransformation(predicate)

    override fun apply(ps: PredicateState): PredicateState {
        val withoutIntrinsics = IntrinsicAdapter.apply(ps)
        return super.apply(withoutIntrinsics)
    }

    private fun createTransformation(predicate: CallPredicate): TransformationResult {
        val state = TransformationState(predicate)
        return try {
            state.transformation()
            state.transformationResult
        } catch (ex: StopInliningException) {
            TransformationResult.Skip
        }
    }

    private fun TransformationResult.applyTransformation(predicate: CallPredicate): Predicate = when (this) {
        is TransformationResult.Skip -> predicate
        is TransformationResult.Action -> {
            for (state in inlinedState) {
                currentBuilder += state
            }
            nothing()
        }
    }

    private fun methodArguments(predicate: CallPredicate): List<TermMapping> {
        val call = predicate.call as CallTerm
        val calledMethod = call.method
        val mappings = arrayListOf<TermMapping>()
        if (!call.isStatic) {
            mappings += TermMapping(call.owner) {
                equalWithSubtyping(term { `this`(call.owner.type) }, it)
            }
        }
        if (predicate.hasLhv) {
            mappings += TermMapping(predicate.lhv) {
                equalWithSubtyping(term { `return`(calledMethod) }, it)
            }
        }

        for ((index, argType) in calledMethod.argTypes.withIndex()) {
            mappings += TermMapping(call.arguments[index]) {
                argumentsEqualWithSubtyping(term { arg(argType.kexType, index) }, it)
            }
        }
        return mappings
    }

    private fun argumentsEqualWithSubtyping(first: Term, second: Term): Boolean {
        if (first !is ArgumentTerm || second !is ArgumentTerm) return false
        if (first.index != second.index) return false
        return equalWithSubtyping(first, second)
    }

    private fun equalWithSubtyping(first: Term, second: Term): Boolean {
        if (first.javaClass != second.javaClass) return false
        if (first.name != second.name || first.subterms != second.subterms) return false
        if (first.type == second.type) return true
        val firstType = first.type.getKfgType(psa.types) as? ClassType ?: return false
        val secondType = second.type.getKfgType(psa.types) as? ClassType ?: return false
        return firstType.klass.isInheritorOf(secondType.klass)
                || secondType.klass.isInheritorOf(firstType.klass) // fixme: type casts needed
    }

    data class TermMapping(val mappedTerm: Term, val predicate: (Term) -> Boolean)

    private class TermRenamer(val suffix: String, val remapping: List<TermMapping>) : Transformer<TermRenamer> {
        private val knownReplacements = hashMapOf<Term, Term>()

        override fun transformTerm(term: Term): Term = knownReplacements.getOrPut(term) { createReplacement(term) }

        private fun createReplacement(term: Term): Term = findReplacement(term) ?: when (term) {
            is ValueTerm, is ArgumentTerm, is ReturnValueTerm -> term { value(term.type, "${term.name}.$suffix") }
            else -> term
        }

        private fun findReplacement(term: Term): Term? {
            val candidates = remapping.filter { it.predicate(term) }
            return when (candidates.size) {
                0 -> null
                1 -> candidates[0].mappedTerm
                else -> throw IllegalStateException("Too many replacement candidates: $term  -> $candidates")
            }
        }
    }

    private object MemorySpaceRemover : Transformer<MemorySpaceRemover> {
        override fun transformTerm(term: Term) = when (term.type) {
            is KexPointer -> term.withMemspace(KexPointer.defaultMemspace)
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

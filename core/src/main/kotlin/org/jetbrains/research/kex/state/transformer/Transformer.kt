package org.jetbrains.research.kex.state.transformer

import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.*
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kfg.ir.Location
import java.util.*

interface Transformer<T : Transformer<T>> {
    /**
     * Stub to return when you want to delete some predicate in predicate state
     * Needed to avoid using nullable types in transformer
     * Should *never* appear outside of transformers
     */
    private object Stub : Predicate() {
        override val type = PredicateType.State()
        override val location = Location()
        override val operands = listOf<Term>()

        override fun print() = "stub"
        override fun <T : Transformer<T>> accept(t: Transformer<T>) = Stub
    }

    fun nothing(): Predicate = Stub

    private inline fun <reified T : TypeInfo> delegate(argument: T): T {
        if (argument is Stub) return argument
        val res = delegate0(argument)
        if (res is Stub) return res
        return delegate1(res)
    }

    private inline fun <reified T : TypeInfo> delegate0(argument: T): T = when (argument) {

        is PredicateState -> when (argument) {
            is NegationState -> transformNegation(argument) as T
            is ChoiceState -> transformChoice(argument) as T
            is ChainState -> transformChain(argument) as T
            is BasicState -> transformBasic(argument) as T
            is CallApproximationState -> transformCallApproximation(argument) as T
            else -> unreachable { log.error("No PredicateState transformer for $argument") }
        }


        is Predicate -> when (argument) {
            is ThrowPredicate -> transformThrow(argument) as T
            is NewPredicate -> transformNew(argument) as T
            is CatchPredicate -> transformCatch(argument) as T
            is NewArrayPredicate -> transformNewArray(argument) as T
            is InequalityPredicate -> transformInequality(argument) as T
            is ArrayStorePredicate -> transformArrayStore(argument) as T
            is ConstantPredicate -> transformConstant(argument) as T
            is CallPredicate -> transformCall(argument) as T
            is EqualityPredicate -> transformEquality(argument) as T
            is FieldStorePredicate -> transformFieldStore(argument) as T
            is DefaultSwitchPredicate -> transformDefaultSwitch(argument) as T
            is BoundStorePredicate -> transformBoundStore(argument) as T
            else -> unreachable { log.error("No Predicate transformer for $argument") }
        }


        is Term -> when (argument) {
            is ConstByteTerm -> transformConstByte(argument) as T
            is FieldLoadTerm -> transformFieldLoad(argument) as T
            is ArgumentTerm -> transformArgument(argument) as T
            is ReturnValueTerm -> transformReturnValue(argument) as T
            is ConstFloatTerm -> transformConstFloat(argument) as T
            is ConstStringTerm -> transformConstString(argument) as T
            is ConstShortTerm -> transformConstShort(argument) as T
            is ArrayLoadTerm -> transformArrayLoad(argument) as T
            is ConstDoubleTerm -> transformConstDouble(argument) as T
            is ArrayLengthTerm -> transformArrayLength(argument) as T
            is CmpTerm -> transformCmp(argument) as T
            is ConstClassTerm -> transformConstClass(argument) as T
            is FieldTerm -> transformField(argument) as T
            is ConstIntTerm -> transformConstInt(argument) as T
            is NegTerm -> transformNeg(argument) as T
            is ValueTerm -> transformValue(argument) as T
            is NullTerm -> transformNull(argument) as T
            is ConstCharTerm -> transformConstChar(argument) as T
            is ArrayIndexTerm -> transformArrayIndex(argument) as T
            is ConstBoolTerm -> transformConstBool(argument) as T
            is UndefTerm -> transformUndef(argument) as T
            is BoundTerm -> transformBound(argument) as T
            is CastTerm -> transformCast(argument) as T
            is CallTerm -> transformCall(argument) as T
            is BinaryTerm -> transformBinary(argument) as T
            is ConstLongTerm -> transformConstLong(argument) as T
            is InstanceOfTerm -> transformInstanceOf(argument) as T
            is LocalObjectTerm -> transformLocalObject(argument) as T
            is IfTerm -> transformIf(argument) as T
            else -> unreachable { log.error("No Term transformer for $argument") }
        }

        else -> unreachable { log.error("No transformer for $argument") }
    }


    private inline fun <reified T : TypeInfo> delegate1(argument: T): T = when (argument) {

        is PredicateState -> when (argument) {
            is NegationState -> transformNegationState(argument) as T
            is ChoiceState -> transformChoiceState(argument) as T
            is ChainState -> transformChainState(argument) as T
            is BasicState -> transformBasicState(argument) as T
            is CallApproximationState -> transformCallApproximationState(argument) as T
            else -> unreachable { log.error("No PredicateState transformer for $argument") }
        }


        is Predicate -> when (argument) {
            is ThrowPredicate -> transformThrowPredicate(argument) as T
            is NewPredicate -> transformNewPredicate(argument) as T
            is CatchPredicate -> transformCatchPredicate(argument) as T
            is NewArrayPredicate -> transformNewArrayPredicate(argument) as T
            is InequalityPredicate -> transformInequalityPredicate(argument) as T
            is ArrayStorePredicate -> transformArrayStorePredicate(argument) as T
            is ConstantPredicate -> transformConstantPredicate(argument) as T
            is CallPredicate -> transformCallPredicate(argument) as T
            is EqualityPredicate -> transformEqualityPredicate(argument) as T
            is FieldStorePredicate -> transformFieldStorePredicate(argument) as T
            is DefaultSwitchPredicate -> transformDefaultSwitchPredicate(argument) as T
            is BoundStorePredicate -> transformBoundStorePredicate(argument) as T
            else -> unreachable { log.error("No Predicate transformer for $argument") }
        }


        is Term -> when (argument) {
            is ConstByteTerm -> transformConstByteTerm(argument) as T
            is FieldLoadTerm -> transformFieldLoadTerm(argument) as T
            is ArgumentTerm -> transformArgumentTerm(argument) as T
            is ReturnValueTerm -> transformReturnValueTerm(argument) as T
            is ConstFloatTerm -> transformConstFloatTerm(argument) as T
            is ConstStringTerm -> transformConstStringTerm(argument) as T
            is ConstShortTerm -> transformConstShortTerm(argument) as T
            is ArrayLoadTerm -> transformArrayLoadTerm(argument) as T
            is ConstDoubleTerm -> transformConstDoubleTerm(argument) as T
            is ArrayLengthTerm -> transformArrayLengthTerm(argument) as T
            is CmpTerm -> transformCmpTerm(argument) as T
            is ConstClassTerm -> transformConstClassTerm(argument) as T
            is FieldTerm -> transformFieldTerm(argument) as T
            is ConstIntTerm -> transformConstIntTerm(argument) as T
            is NegTerm -> transformNegTerm(argument) as T
            is ValueTerm -> transformValueTerm(argument) as T
            is NullTerm -> transformNullTerm(argument) as T
            is ConstCharTerm -> transformConstCharTerm(argument) as T
            is ArrayIndexTerm -> transformArrayIndexTerm(argument) as T
            is ConstBoolTerm -> transformConstBoolTerm(argument) as T
            is UndefTerm -> transformUndefTerm(argument) as T
            is BoundTerm -> transformBoundTerm(argument) as T
            is CastTerm -> transformCastTerm(argument) as T
            is CallTerm -> transformCallTerm(argument) as T
            is BinaryTerm -> transformBinaryTerm(argument) as T
            is ConstLongTerm -> transformConstLongTerm(argument) as T
            is InstanceOfTerm -> transformInstanceOfTerm(argument) as T
            is LocalObjectTerm -> transformLocalObjectTerm(argument) as T
            is IfTerm -> transformIfTerm(argument) as T
            else -> unreachable { log.error("No Term transformer for $argument") }
        }

        else -> unreachable { log.error("No transformer for $argument") }
    }

    fun apply(ps: PredicateState) = transform(ps).simplify()

    ////////////////////////////////////////////////////////////////////
    // PredicateState
    ////////////////////////////////////////////////////////////////////
    fun transform(ps: PredicateState) = transformBase(ps)

    fun transformBase(ps: PredicateState): PredicateState {
        val res = delegate(ps)
        return transformPredicateState(res)
    }

    fun transformPredicateState(ps: PredicateState) = ps

    fun transformBasic(ps: BasicState): PredicateState = ps.map { p -> transformBase(p) }.filterNot { it is Stub }
    fun transformChain(ps: ChainState): PredicateState = ps.fmap { e -> transformBase(e) }
    fun transformChoice(ps: ChoiceState): PredicateState = ps.fmap { e -> transformBase(e) }
    fun transformNegation(ps: NegationState): PredicateState = ps.fmap { e -> transformBase(e) }
    fun transformCallApproximation(ps: CallApproximationState): PredicateState = ps.fmap { e -> transformBase(e) }

    fun transformBasicState(ps: BasicState): PredicateState = ps
    fun transformChainState(ps: ChainState): PredicateState = ps
    fun transformChoiceState(ps: ChoiceState): PredicateState = ps
    fun transformNegationState(ps: NegationState): PredicateState = ps
    fun transformCallApproximationState(ps: CallApproximationState): PredicateState = ps

    fun transform(predicate: Predicate) = transformBase(predicate)
    fun transformBase(predicate: Predicate): Predicate {
        val res = delegate(predicate)
        return transformPredicate(res)
    }

    ////////////////////////////////////////////////////////////////////
    // Predicate
    ////////////////////////////////////////////////////////////////////
    fun transformPredicate(predicate: Predicate) = predicate

    fun transformArrayStore(predicate: ArrayStorePredicate): Predicate = predicate.accept(this)
    fun transformBoundStore(predicate: BoundStorePredicate): Predicate = predicate.accept(this)
    fun transformCall(predicate: CallPredicate): Predicate = predicate.accept(this)
    fun transformCatch(predicate: CatchPredicate): Predicate = predicate.accept(this)
    fun transformDefaultSwitch(predicate: DefaultSwitchPredicate): Predicate = predicate.accept(this)
    fun transformInequality(predicate: InequalityPredicate): Predicate = predicate.accept(this)
    fun transformEquality(predicate: EqualityPredicate): Predicate = predicate.accept(this)
    fun transformFieldStore(predicate: FieldStorePredicate): Predicate = predicate.accept(this)
    fun transformNewArray(predicate: NewArrayPredicate): Predicate = predicate.accept(this)
    fun transformNew(predicate: NewPredicate): Predicate = predicate.accept(this)
    fun transformThrow(predicate: ThrowPredicate): Predicate = predicate.accept(this)
    fun transformConstant(predicate: ConstantPredicate): Predicate = predicate.accept(this)

    fun transformArrayStorePredicate(predicate: ArrayStorePredicate): Predicate = predicate
    fun transformBoundStorePredicate(predicate: BoundStorePredicate): Predicate = predicate
    fun transformCallPredicate(predicate: CallPredicate): Predicate = predicate
    fun transformCatchPredicate(predicate: CatchPredicate): Predicate = predicate
    fun transformDefaultSwitchPredicate(predicate: DefaultSwitchPredicate): Predicate = predicate
    fun transformInequalityPredicate(predicate: InequalityPredicate): Predicate = predicate
    fun transformEqualityPredicate(predicate: EqualityPredicate): Predicate = predicate
    fun transformFieldStorePredicate(predicate: FieldStorePredicate): Predicate = predicate
    fun transformNewArrayPredicate(predicate: NewArrayPredicate): Predicate = predicate
    fun transformNewPredicate(predicate: NewPredicate): Predicate = predicate
    fun transformThrowPredicate(predicate: ThrowPredicate): Predicate = predicate
    fun transformConstantPredicate(predicate: ConstantPredicate): Predicate = predicate.accept(this)

    ////////////////////////////////////////////////////////////////////
    // Term
    ////////////////////////////////////////////////////////////////////
    fun transform(term: Term) = transformBase(term)

    fun transformBase(term: Term): Term {
        val res = delegate(term)
        return transformTerm(res)
    }

    fun transformTerm(term: Term) = term

    fun transformArgument(term: ArgumentTerm): Term = term.accept(this)
    fun transformArrayIndex(term: ArrayIndexTerm): Term = term.accept(this)
    fun transformArrayLength(term: ArrayLengthTerm): Term = term.accept(this)
    fun transformArrayLoad(term: ArrayLoadTerm): Term = term.accept(this)
    fun transformBinary(term: BinaryTerm): Term = term.accept(this)
    fun transformBound(term: BoundTerm): Term = term.accept(this)
    fun transformCall(term: CallTerm): Term = term.accept(this)
    fun transformCast(term: CastTerm): Term = term.accept(this)
    fun transformCmp(term: CmpTerm): Term = term.accept(this)
    fun transformConstBool(term: ConstBoolTerm): Term = term.accept(this)
    fun transformConstByte(term: ConstByteTerm): Term = term.accept(this)
    fun transformConstChar(term: ConstCharTerm): Term = term.accept(this)
    fun transformConstClass(term: ConstClassTerm): Term = term.accept(this)
    fun transformConstDouble(term: ConstDoubleTerm): Term = term.accept(this)
    fun transformConstFloat(term: ConstFloatTerm): Term = term.accept(this)
    fun transformConstInt(term: ConstIntTerm): Term = term.accept(this)
    fun transformConstLong(term: ConstLongTerm): Term = term.accept(this)
    fun transformConstShort(term: ConstShortTerm): Term = term.accept(this)
    fun transformConstString(term: ConstStringTerm): Term = term.accept(this)
    fun transformFieldLoad(term: FieldLoadTerm): Term = term.accept(this)
    fun transformField(term: FieldTerm): Term = term.accept(this)
    fun transformInstanceOf(term: InstanceOfTerm): Term = term.accept(this)
    fun transformNeg(term: NegTerm): Term = term.accept(this)
    fun transformNull(term: NullTerm): Term = term.accept(this)
    fun transformReturnValue(term: ReturnValueTerm): Term = term.accept(this)
    fun transformValue(term: ValueTerm): Term = term.accept(this)
    fun transformUndef(term: UndefTerm): Term = term.accept(this)
    fun transformLocalObject(term: LocalObjectTerm): Term = term.accept(this)
    fun transformIf(term: IfTerm): Term = term.accept(this)

    fun transformArgumentTerm(term: ArgumentTerm): Term = term
    fun transformArrayIndexTerm(term: ArrayIndexTerm): Term = term
    fun transformArrayLengthTerm(term: ArrayLengthTerm): Term = term
    fun transformArrayLoadTerm(term: ArrayLoadTerm): Term = term
    fun transformBinaryTerm(term: BinaryTerm): Term = term
    fun transformBoundTerm(term: BoundTerm): Term = term
    fun transformCallTerm(term: CallTerm): Term = term
    fun transformCastTerm(term: CastTerm): Term = term
    fun transformCmpTerm(term: CmpTerm): Term = term
    fun transformConstBoolTerm(term: ConstBoolTerm): Term = term
    fun transformConstByteTerm(term: ConstByteTerm): Term = term
    fun transformConstCharTerm(term: ConstCharTerm): Term = term
    fun transformConstClassTerm(term: ConstClassTerm): Term = term
    fun transformConstDoubleTerm(term: ConstDoubleTerm): Term = term
    fun transformConstFloatTerm(term: ConstFloatTerm): Term = term
    fun transformConstIntTerm(term: ConstIntTerm): Term = term
    fun transformConstLongTerm(term: ConstLongTerm): Term = term
    fun transformConstShortTerm(term: ConstShortTerm): Term = term
    fun transformConstStringTerm(term: ConstStringTerm): Term = term
    fun transformFieldLoadTerm(term: FieldLoadTerm): Term = term
    fun transformFieldTerm(term: FieldTerm): Term = term
    fun transformInstanceOfTerm(term: InstanceOfTerm): Term = term
    fun transformNegTerm(term: NegTerm): Term = term
    fun transformNullTerm(term: NullTerm): Term = term
    fun transformReturnValueTerm(term: ReturnValueTerm): Term = term
    fun transformValueTerm(term: ValueTerm): Term = term
    fun transformUndefTerm(term: UndefTerm): Term = term
    fun transformLocalObjectTerm(term: LocalObjectTerm): Term = term
    fun transformIfTerm(term: IfTerm): Term = term
}

interface RecollectingTransformer<T> : Transformer<RecollectingTransformer<T>> {
    val builders: Deque<StateBuilder>

    val currentBuilder: StateBuilder
        get() = builders.last

    val state: PredicateState
        get() = currentBuilder.apply()

    override fun apply(ps: PredicateState): PredicateState {
        super.transform(ps)
        return state.simplify()
    }

    override fun transformChoice(ps: ChoiceState): PredicateState {
        val newChoices = arrayListOf<PredicateState>()
        for (choice in ps.choices) {
            builders.add(StateBuilder())
            super.transformBase(choice)

            newChoices.add(currentBuilder.apply())
            builders.pollLast()
        }
        currentBuilder += newChoices
        return ps
    }

    override fun transformPredicate(predicate: Predicate): Predicate {
        val result = super.transformPredicate(predicate)
        if (result != nothing()) currentBuilder += result
        return result
    }

    override fun transformNegation(ps: NegationState): PredicateState {
        val nestedState = transformPs(ps.predicateState)
        currentBuilder += NegationState(nestedState)
        return ps
    }

    override fun transformCallApproximation(ps: CallApproximationState): PredicateState {
        val newPre = ps.preconditions.map { transformPs(it) }
        val newPost = ps.postconditions.map { transformPs(it) }
        val newCallState = transformPs(ps.callState)
        val newDefaultPost = transformPs(ps.defaultPostcondition)
        currentBuilder += CallApproximationState(newPre, newPost, newCallState, newDefaultPost, ps.call)
        return ps
    }

    fun transformPs(ps: PredicateState): PredicateState {
        builders.addLast(StateBuilder())
        super.transformBase(ps)
        return builders.removeLast().apply()
    }
}

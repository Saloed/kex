package org.jetbrains.research.kex.smt.z3.fixpoint.converter

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.CallApproximationState
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.ConstantPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kfg.type.TypeFactory

open class Z3ConverterWithCallMemory(tf: TypeFactory, val memoryVersionInfo: MemoryVersionInfo) : Z3Converter(tf) {
    private var callCounter = 1

    data class CallInfo(
            val index: Int,
            val predicate: CallPredicate,
            val result: Z3Bool,
            val resultTerm: Term
    )

    val callInfo = hashMapOf<CallPredicate, CallInfo>()
    fun getCallsInfo(): List<CallInfo> = callInfo.values.toList()
    protected val callStack = dequeOf<CallPredicate>()

    override fun convert(callApproximation: CallApproximationState, ef: Z3ExprFactory, ctx: Z3Context, extractPath: Boolean): Bool_ {
        if (extractPath) return ef.makeTrue()
        val call = callApproximation.call
        callStack.addLast(call)
        if (call !in callInfo) {
            callInfo[call] = processCall(call, ef, ctx)
        }
        val callInfo = callInfo[call] ?: throw IllegalStateException("Impossible")

        val preState = convert(PredicateStateWithPath.choice(callApproximation.preconditions).state, ef, ctx, false)
        val preconditions = convertChoices(callApproximation.preconditions.map { it.path }, ef, ctx, false)
        val callState = convert(callApproximation.callState, ef, ctx, false)
        ctx.resetMemoryToVersion(callInfo.predicate.memoryVersion, memoryVersionInfo)
        val postState = convert(PredicateStateWithPath.choice(callApproximation.postconditions + callApproximation.defaultPostcondition).state, ef, ctx, false)
        val allPostConditions = convertChoices((callApproximation.postconditions + callApproximation.defaultPostcondition).map { it.path }, ef, ctx, false)
        val postconditions = allPostConditions.dropLast(1)
        val defaultPost = allPostConditions.last()
        val defaultCase = callState and defaultPost
        callStack.removeLast()
        val approximations = preconditions.zip(postconditions)
                .map { it.first implies it.second }
                .fold(ef.makeTrue()) { acc, cond -> acc and cond }
        val defaultApproximation = preconditions
                .fold(ef.makeFalse()) { acc, cond -> acc or cond }
                .not() implies defaultCase
        return preState and postState and approximations and defaultApproximation
    }

    override fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context): Bool_ {
        if (callStack.isEmpty()) throw IllegalStateException("No calls in stack")
        if (call !in callStack) throw IllegalStateException("Call not in stack")
        if (callStack.size > 1) log.warn("Call approximation stack size ${callStack.size}")
        val callInfo = callInfo[call] ?: throw IllegalStateException("Impossible")
        val callArguments = call.call.subterms.map { convert(it, ef, ctx) }
        val argumentsAxioms = callArguments.map { it.axiomExpr() }
        return argumentsAxioms.fold(callInfo.result) { res, ax -> res.withAxiom(ax) }
    }

    internal fun processCall(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context): CallInfo {
        val callIdx = callCounter++
        val callType = when {
            call.hasLhv -> call.lhv.type
            else -> (call.call as CallTerm).method.returnType.kexType
        }
        val callVariable = term { value(callType, "call__${callIdx}__result") }
        val callReplacement = when {
            call.hasLhv -> EqualityPredicate(call.lhv, callVariable, call.type, call.location)
            else -> ConstantPredicate(true, call.type, call.location)
        }
        val result = convert(callReplacement, ef, ctx)
        return CallInfo(callIdx, call, result, callVariable)
    }

}

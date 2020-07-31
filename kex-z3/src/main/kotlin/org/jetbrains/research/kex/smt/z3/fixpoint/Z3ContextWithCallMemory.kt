package org.jetbrains.research.kex.smt.z3.fixpoint

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.CallApproximationState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.ConstantPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kfg.type.TypeFactory

class Z3ContextWithCallMemory(tf: TypeFactory) : Z3Converter(tf) {
    private var callCounter = 0

    data class CallInfo(
            val index: Int,
            val predicate: CallPredicate,
            val result: Z3Bool,
            val resultTerm: Term,
            val memoryBefore: Map<String, VersionedMemory>,
            val memoryAfter: Map<String, VersionedMemory>
    )

    val callInfo = hashMapOf<CallPredicate, CallInfo>()
    fun getCallsInfo(): List<CallInfo> = callInfo.values.toList()
    private val callStack = dequeOf<CallPredicate>()

    override fun convert(callApproximation: CallApproximationState, ef: Z3ExprFactory, ctx: Z3Context, extractPath: Boolean): Bool_ {
        val call = callApproximation.call
        callStack.addLast(call)
        if (call !in callInfo) {
            callInfo[call] = processCall(call, ef, ctx)
        }
        val callInfo = callInfo[call] ?: throw IllegalStateException("Impossible")
        val preconditions = callApproximation.preconditions.map { convert(it, ef, ctx, extractPath) }
        val callState = convert(callApproximation.callState, ef, ctx, extractPath)
        val cases: Map<Z3Bool, Z3Bool>
        val defaultCase: Z3Bool
        ctx.setMemory(callInfo.memoryAfter)
        val postconditions = callApproximation.postconditions.map { convert(it, ef, ctx, extractPath) }
        val defaultPost = convert(callApproximation.defaultPostcondition, ef, ctx, extractPath)
        cases = preconditions.zip(postconditions).toMap()
        defaultCase = callState and defaultPost
        callStack.removeLast()
        return ef.switch(cases, defaultCase)
    }

    override fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context): Bool_ {
        if (callStack.isEmpty()) throw IllegalStateException("No calls in stack")
        if (call !in callStack) throw IllegalStateException("Call not in stack")
        if (callStack.size > 1) log.warn("Call approximation stack size ${callStack.size}")
        val callInfo = callInfo[call] ?: throw IllegalStateException("Impossible")
        val callArguments = call.call.subterms.map { convert(it, ef, ctx) }
        return callInfo.result
    }

    private fun Z3Context.currentMemory() = accessRawMemories().toMap()
    private fun Z3Context.setMemory(memory: Map<String, VersionedMemory>) {
        val memories = accessRawMemories()
        for ((name, mem) in memory) {
            memories[name] = mem
        }
    }

    private fun Z3Context.generateEmptyMemory(idx: Int) {
        val memories = accessRawMemories()
        for ((name, current) in memories) {
            memories[name] = VersionedMemory(factory.makeEmptyMemory("call__${idx}__${name}", current.type), current.version + 1, current.type)
        }
    }

    private fun processCall(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context): CallInfo {
        val callIdx = callCounter++
        val memoriesBefore = ctx.currentMemory()
        ctx.generateEmptyMemory(callIdx)
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
        val afterMemory = ctx.currentMemory()
        ctx.setMemory(memoriesBefore)
        return CallInfo(callIdx, call, result, callVariable, memoriesBefore, afterMemory)
    }

}

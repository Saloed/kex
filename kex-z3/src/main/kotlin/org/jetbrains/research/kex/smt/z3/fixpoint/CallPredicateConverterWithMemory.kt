package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.ConstantPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term

class CallPredicateConverterWithMemory : CallPredicateConverter {
    private var callCounter = 0

    data class CallInfo(
            val index: Int,
            val predicate: CallPredicate,
            val subterms: List<Z3ValueExpr>,
            val result: Z3Bool,
            val resultTerm: Term,
            val memoryBefore: Map<String, VersionedMemory>,
            val memoryAfter: Map<String, VersionedMemory>
    )

    val callInfo = hashMapOf<CallPredicate, CallInfo>()
    fun getCallsInfo(): List<CallInfo> = callInfo.values.toList()

    override fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool {
        if (call !in callInfo) {
            callInfo[call] = processCall(call, ef, ctx, converter)
        }
        val info = callInfo[call] ?: throw IllegalStateException("Impossible")
        ctx.setMemory(info.memoryAfter)
        return info.result
    }

    private fun Z3Context.currentMemory() = accessRawMemories().toMap()
    private fun Z3Context.setMemory(memory: Map<String, VersionedMemory>) {
        val memories = accessRawMemories()
        for ((name, mem) in memory) {
            memories[name] = mem
        }
    }

    private fun Z3Context.cleanupMemory(idx: Int) {
        val memories = accessRawMemories()
        for ((name, _) in memories) {
            memories[name] = VersionedMemory(factory.makeEmptyMemory("call__${idx}__${name}"))
        }
    }

    private fun processCall(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): CallInfo {
        val callIdx = callCounter++
        val subterms = call.call.subterms.map { converter.convert(it, ef, ctx) }
        val memoriesBefore = ctx.currentMemory()
        ctx.cleanupMemory(callIdx)
        val callType = when {
            call.hasLhv -> call.lhv.type
            else -> (call.call as CallTerm).method.returnType.kexType
        }
        val callVariable = term { value(callType, "call__${callIdx}__result") }
        val callReplacement = when {
            call.hasLhv -> EqualityPredicate(call.lhv, callVariable, call.type, call.location)
            else -> ConstantPredicate(true, call.type, call.location)
        }
        val result = converter.convert(callReplacement, ef, ctx)
        val afterMemory = ctx.currentMemory()
        return CallInfo(callIdx, call, subterms, result, callVariable, memoriesBefore, afterMemory)
    }

}

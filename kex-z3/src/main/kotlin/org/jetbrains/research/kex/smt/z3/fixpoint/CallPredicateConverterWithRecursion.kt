package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.ktype.KexPointer
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.memspace

class CallPredicateConverterWithRecursion(val recursiveCalls: List<CallPredicate>, val predicateName: String) {

    lateinit var termVars: MutableMap<Int, Term>
    lateinit var memoryVars: MutableMap<Int, Int>

    fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool =
            when {
                recursiveCalls.any {
                    //fixme: compare by methods because of memspace ...
                    (it.call as CallTerm).method == (call.call as CallTerm).method
                } -> buildPredicate(call, ef, ctx, converter)
                else -> ef.makeTrue()
            }

    fun initVariableOrder(callPredicate: CallPredicate) {
        val receiver = callPredicate.lhvUnsafe
                ?: throw IllegalStateException("Call prototype must have a receiver")
        termVars = hashMapOf()
        var idx = 0
        for (term in (callArguments(callPredicate.call as CallTerm) + receiver)) {
            termVars[idx] = term
            idx++
        }
        memoryVars = hashMapOf()
        for (memspace in memspaces(callPredicate.call as CallTerm)) {
            memoryVars[idx] = memspace
            idx++
        }
    }


    fun buildPredicate(callPredicate: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool {
        val receiver = callPredicate.lhvUnsafe?.let { converter.convert(it, ef, ctx) }
                ?: ef.dummyReceiver(callPredicate.call as CallTerm)
        val arguments = callArguments(callPredicate.call as CallTerm).map { converter.convert(it, ef, ctx) }
        val memories = memspaces(callPredicate.call as CallTerm).map { ctx.getMemory(it) }
        val memoryArrays = memories.map { it.memory.inner }
        // fixme: MEMORY

        val predicateArguments = arguments + receiver + memoryArrays
        val predicateSorts = predicateArguments.map { it.getSort() }
        val predicateAxioms = predicateArguments.map { it.axiom }
        val predicateExprs = predicateArguments.map { it.expr }
        val predicate = ef.ctx.mkFuncDecl(predicateName, predicateSorts.toTypedArray(), ef.ctx.mkBoolSort())
        val predicateApplication = ef.ctx.mkApp(predicate, *predicateExprs.toTypedArray()) as BoolExpr
        return Z3Bool(ef.ctx, predicateApplication, spliceAxioms(ef.ctx, predicateAxioms))
    }

    private fun callArguments(call: CallTerm) = listOf(call.owner) + call.arguments
    private fun memspaces(call: CallTerm) = callArguments(call).filter { it.type is KexPointer }.map { it.memspace }
    private fun Z3ExprFactory.dummyReceiver(call: CallTerm) = getVarByTypeAndName(call.method.returnType.kexType, "dummy_result_receiver", fresh = true)

}

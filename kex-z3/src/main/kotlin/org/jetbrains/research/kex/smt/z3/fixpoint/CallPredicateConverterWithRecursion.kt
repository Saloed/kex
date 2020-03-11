package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.ktype.KexPointer
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
                recursiveCalls.any { (it.call as CallTerm).method == (call.call as CallTerm).method } -> buildPredicate(call, ef, ctx, converter)
                else -> ef.makeTrue()
            }

    fun initVariableOrder(callPredicate: CallPredicate) {
        val call = callPredicate.call as CallTerm
        if (!call.isStatic) {
            TODO("Non static recursive call")
        }
        val receiver = callPredicate.lhvUnsafe
                ?: TODO("Recursive call without result receiver")
        val memspaces = call.arguments.filter { it.type is KexPointer }.map { it.memspace }

        termVars = hashMapOf()
        var idx = 0
        for (term in (call.arguments + receiver)) {
            termVars[idx] = term
            idx++
        }
        memoryVars = hashMapOf()
        for (memspace in memspaces) {
            memoryVars[idx] = memspace
            idx++
        }
    }

    fun buildPredicate(callPredicate: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool {
        val call = callPredicate.call as CallTerm
        if (!call.isStatic) {
            TODO("Non static recursive call")
        }
        val receiver = callPredicate.lhvUnsafe?.let { converter.convert(it, ef, ctx) }
        val arguments = call.arguments.map { converter.convert(it, ef, ctx) }
        if (receiver == null) {
            TODO("Recursive call without result receiver")
        }
        val memspaces = call.arguments.filter { it.type is KexPointer }.map { it.memspace }
        val memories = memspaces.map { ctx.getMemory(it) }
        val memoryArrays = memories.map { it.memory.inner }

        val predicateArguments = arguments + receiver + memoryArrays
        val predicateSorts = predicateArguments.map { it.getSort() }
        val predicateAxioms = predicateArguments.map { it.axiom }
        val predicateExprs = predicateArguments.map { it.expr }
        val predicate = ef.ctx.mkFuncDecl(predicateName, predicateSorts.toTypedArray(), ef.ctx.mkBoolSort())
        val predicateApplication = ef.ctx.mkApp(predicate, *predicateExprs.toTypedArray()) as BoolExpr
        return Z3Bool(ef.ctx, predicateApplication, spliceAxioms(ef.ctx, predicateAxioms))
    }


}

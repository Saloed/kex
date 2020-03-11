package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm

class CallPredicateConverterWithRecursion(val recursiveCalls: List<CallPredicate>, val predicateName: String) {
    fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool =
            when {
                call in recursiveCalls -> buildPredicate(call, ef, ctx, converter)
                else -> ef.makeTrue()
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

        val predicateArguments = arguments + receiver
        val predicateSorts = predicateArguments.map { it.getSort() }
        val predicateAxioms = predicateArguments.map { it.axiom }
        val predicateExprs = predicateArguments.map { it.expr }
        val predicate = ef.ctx.mkFuncDecl(predicateName, predicateSorts.toTypedArray(), ef.ctx.mkBoolSort())
        val predicateApplication = ef.ctx.mkApp(predicate, *predicateExprs.toTypedArray()) as BoolExpr
        return Z3Bool(ef.ctx, predicateApplication, spliceAxioms(ef.ctx, predicateAxioms))
    }


}

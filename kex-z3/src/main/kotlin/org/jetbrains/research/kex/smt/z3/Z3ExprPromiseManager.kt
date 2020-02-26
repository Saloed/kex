package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.Sort

class Z3ExprPromiseManager(val ctx: Context) {
    private data class Promise(val pc: Expr, val sort: Sort, val eval: () -> Expr)

    private val promises = mutableListOf<Promise>()

    fun createPromise(sort: Sort, lazy: () -> Expr): Expr {
        val pc = ctx.mkFreshConst("placeholder", sort)
        promises.add(Promise(pc, sort, lazy))
        return pc
    }

    fun resolvePromises(expr: Expr): Expr {
        val placeholders = promises.map { it.pc }.toTypedArray()
        val values = promises.map { it.eval() }.toTypedArray()
        return expr.substitute(placeholders, values)
    }
}


open class Z3ContextWithPromises : Context() {
    val promiseManager = Z3ExprPromiseManager(this)
}

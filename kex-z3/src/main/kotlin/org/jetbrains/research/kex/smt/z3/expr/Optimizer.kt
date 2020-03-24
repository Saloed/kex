package org.jetbrains.research.kex.smt.z3.expr

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.Quantifier

class Optimizer(val ctx: Context) {

    // This hack speedup fixpoint solver exponentially
    inner class TrickyHack1 : Z3ExpressionVisitor {
        private val pendingSubstitutions = arrayListOf<Pair<Expr, Expr>>()

        override fun visitBoolExpr(expr: BoolExpr) {
            if (!expr.isOr) return super.visitBoolExpr(expr)
            if (expr.numArgs <= 1) return super.visitBoolExpr(expr)
            val args = expr.args
            val andClauses = args.filterIsInstance<BoolExpr>().filter { it.isAnd }
            val candidates = andClauses
                    .map { it.args.filter { isCandidate(it) }.filterIsInstance<BoolExpr>() }
            //todo: check usges in other branches
            if (candidates.all { it.isEmpty() }) return super.visitBoolExpr(expr)
            val expressionsToOptimize = candidates.flatten()
                    .groupBy { it }
                    .mapValues { (_, v) -> v.size }
                    .filter { it.value > 1 }.keys.toTypedArray()
            val optimizedExpression = ctx.mkAnd(*expressionsToOptimize, expr)
            pendingSubstitutions.add(expr to optimizedExpression)
        }

        private fun isCandidate(expr: Expr) = expr.isEq && expr.numArgs == 2 && expr.args[0].let { it is BoolExpr && it.isVar }

        fun optimize(expr: Expr): Expr {
            visit(expr)
            val replaceFrom = pendingSubstitutions.map { it.first }.toTypedArray()
            val replaceTo = pendingSubstitutions.map { it.second }.toTypedArray()
            return when (expr) {
                is Quantifier -> substituteQuantifier(expr, replaceFrom, replaceTo)
                else -> expr.substitute(replaceFrom, replaceTo)
            }
        }

        private fun substituteQuantifier(expr: Quantifier, from: Array<Expr>, to: Array<Expr>) = ctx.mkQuantifier(
                expr.isUniversal,
                expr.boundVariableSorts,
                expr.boundVariableNames,
                expr.body.substitute(from, to),
                expr.numPatterns,
                expr.patterns,
                null,
                null,
                null
        )
    }

    fun apply(expr: BoolExpr): BoolExpr = TrickyHack1().optimize(expr) as BoolExpr

}
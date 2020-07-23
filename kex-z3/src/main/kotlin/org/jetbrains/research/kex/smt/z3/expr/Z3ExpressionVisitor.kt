package org.jetbrains.research.kex.smt.z3.expr

import com.microsoft.z3.*

interface Z3ExpressionVisitor {
    fun visit(expr: Expr): Unit = when (expr) {
        is SeqExpr -> visitSeqExpr(expr)
        is DatatypeExpr -> visitDatatypeExpr(expr)
        is ReExpr -> visitReExpr(expr)
        is FPRMExpr -> when (expr) {
            is FPRMNum -> visitFPRMNum(expr)
            else -> visitFPRMExpr(expr)
        }
        is FiniteDomainExpr -> when (expr) {
            is FiniteDomainNum -> visitFiniteDomainNum(expr)
            else -> visitFiniteDomainExpr(expr)
        }
        is ArrayExpr -> when (expr) {
            is Lambda -> visitLambda(expr)
            else -> visitArrayExpr(expr)
        }
        is BoolExpr -> when (expr) {
            is Quantifier -> visitQuantifier(expr)
            else -> visitBoolExpr(expr)
        }
        is BitVecExpr -> when (expr) {
            is BitVecNum -> visitBitVecNum(expr)
            else -> visitBitVecExpr(expr)
        }
        is FPExpr -> when (expr) {
            is FPNum -> visitFPNum(expr)
            else -> visitFPExpr(expr)
        }
        is ArithExpr -> when (expr) {
            is IntExpr -> when (expr) {
                is IntNum -> visitIntNum(expr)
                else -> visitIntExpr(expr)
            }
            is RealExpr -> when (expr) {
                is RatNum -> visitRatNum(expr)
                else -> visitRealExpr(expr)
            }
            is AlgebraicNum -> visitAlgebraicNum(expr)
            else -> visitArithExpr(expr)
        }
        else -> visitExpr(expr)
    }

    fun visitArithExpr(expr: ArithExpr) = visitExpr(expr)
    fun visitAlgebraicNum(expr: AlgebraicNum) = visitArithExpr(expr)
    fun visitRealExpr(expr: RealExpr) = visitArithExpr(expr)
    fun visitRatNum(expr: RatNum) = visitRealExpr(expr)
    fun visitIntExpr(expr: IntExpr) = visitArithExpr(expr)
    fun visitIntNum(expr: IntNum) = visitIntExpr(expr)
    fun visitFPExpr(expr: FPExpr) = visitExpr(expr)
    fun visitFPNum(expr: FPNum) = visitFPExpr(expr)
    fun visitBitVecExpr(expr: BitVecExpr) = visitExpr(expr)
    fun visitBitVecNum(expr: BitVecNum) = visitBitVecExpr(expr)
    fun visitBoolExpr(expr: BoolExpr) = visitExpr(expr)
    fun visitQuantifier(expr: Quantifier) = visitBoolExpr(expr)
    fun visitArrayExpr(expr: ArrayExpr) = visitExpr(expr)
    fun visitLambda(expr: Lambda) = visitArrayExpr(expr)
    fun visitFiniteDomainExpr(expr: FiniteDomainExpr) = visitExpr(expr)
    fun visitFiniteDomainNum(expr: FiniteDomainNum) = visitFiniteDomainExpr(expr)
    fun visitReExpr(expr: ReExpr) = visitExpr(expr)
    fun visitDatatypeExpr(expr: DatatypeExpr) = visitExpr(expr)
    fun visitSeqExpr(expr: SeqExpr) = visitExpr(expr)
    fun visitFPRMExpr(expr: FPRMExpr) = visitExpr(expr)
    fun visitFPRMNum(expr: FPRMNum) = visitFPRMExpr(expr)
    fun visitVariable(expr: Expr) = Unit
    fun visitExpr(expr: Expr) = when {
        expr is Quantifier -> visit(expr.body)
        expr.isVar -> visitVariable(expr)
        expr.numArgs > 0 -> expr.args.forEach { visit(it) }
        else -> Unit
    }

    fun substitute(ctx: Context, expr: Expr, from: Array<Expr>, to: Array<Expr>) = when (expr) {
        is Quantifier -> substituteQuantifier(ctx, expr, from, to)
        else -> expr.substitute(from, to)
    }

    private fun substituteQuantifier(ctx: Context, expr: Quantifier, from: Array<Expr>, to: Array<Expr>) = ctx.mkQuantifier(
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

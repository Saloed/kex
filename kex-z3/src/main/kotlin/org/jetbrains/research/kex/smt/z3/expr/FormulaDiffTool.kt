package org.jetbrains.research.kex.smt.z3.expr

import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.Quantifier
import org.jetbrains.research.kex.util.DiffNode
import org.jetbrains.research.kex.util.DiffSelector
import org.jetbrains.research.kex.util.DiffTool
import kotlin.math.max


@Suppress("unused")
class FormulaDiffTool(val ctx: Context, first: Expr, second: Expr) : DiffTool<Expr>(first, second) {
    override fun diff(parent: DiffNode<Expr>?, selector: DiffSelector<Expr>?, first: Expr, second: Expr): DiffNode<Expr> = when {
        first == second -> DiffNode.Same(parent, selector)
        first.astKind != second.astKind -> DiffNode.Different(parent, selector)
        !first.isExpr -> DiffNode.Different(parent, selector)
        first.sort != second.sort -> DiffNode.Different(parent, selector)
        first.isApp && first.funcDecl != second.funcDecl -> DiffNode.Different(parent, selector)
        else -> expressionChildrenDiff(DiffNode.Different(parent, selector), first, second)
    }

    private fun expressionChildrenDiff(node: DiffNode<Expr>, first: Expr, second: Expr): DiffNode<Expr> {
        if (first.isQuantifier) {
            val selector = QuantifierBodySelector(ctx)
            node.children += diff(node, selector, selector.get(first), selector.get(second))
            return node
        }
        val firstNumArgs = max(0, first.numArgs)
        val secondNumArgs = max(0, first.numArgs)
        if (firstNumArgs != secondNumArgs) throw IllegalStateException("Same functions with different arguments number")
        for (argIndex in 0 until firstNumArgs) {
            val selector = ExprSelector(argIndex)
            node.children += diff(node, selector, selector.get(first), selector.get(second))
        }
        return node
    }

    override fun createDiffPlaceholder(left: Expr, right: Expr): Expr {
        val diffFunDecl = ctx.mkFreshFuncDecl("diff", arrayOf(left.sort, right.sort), left.sort)
        return ctx.mkApp(diffFunDecl, left, right)
    }

    companion object {
        fun diff(ctx: Context, first: Expr, second: Expr): Expr = FormulaDiffTool(ctx, first, second).diff().simplify()
    }
}

private open class ExprSelector(val argIndex: Int) : DiffSelector<Expr> {
    override fun get(expr: Expr): Expr = when {
        argIndex >= expr.numArgs -> throw IllegalStateException("Unable to apply $this to $expr ")
        else -> expr.args[argIndex]
    }

    override fun set(expr: Expr, value: Expr): Expr = when {
        argIndex >= expr.numArgs -> throw IllegalStateException("Unable to apply $this to $expr ")
        else -> {
            val args = expr.args
            args[argIndex] = value
            expr.update(args)
        }
    }
}

private class QuantifierBodySelector(val ctx: Context) : ExprSelector(0) {
    override fun get(expr: Expr): Expr = (expr as Quantifier).body
    override fun set(expr: Expr, value: Expr): Expr {
        expr as Quantifier
        return Quantifier.of(ctx, expr.isUniversal, expr.boundVariableSorts, expr.boundVariableNames,
                value, expr.numPatterns, expr.patterns, null, null, null)
    }
}

package org.jetbrains.research.kex.smt.z3.expr

import com.abdullin.kthelper.collection.dequeOf
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import kotlin.math.max
import java.util.*

class FormulaDiffTool(val ctx: Context, val first: Expr, val second: Expr) : Z3ExpressionVisitor {
    fun diff(): Expr {
        val diffNodes = diff(null, null, first, second).terminalNodes().filterIsInstance<DiffNode.Different>()
        var result = first
        for (node in diffNodes) {
            val path = node.path()
            val firstExpr = path.eval(first)
            val secondExpr = path.eval(second)
            val diffFunDecl = ctx.mkFreshFuncDecl("diff", arrayOf(firstExpr.sort, secondExpr.sort), firstExpr.sort)
            val diffApp = ctx.mkApp(diffFunDecl, firstExpr, secondExpr)
            result = path.replaceAtPath(result, diffApp)
        }
        return result.simplify()
    }

    private fun diff(parent: DiffNode?, selector: ExprSelector?, first: Expr, second: Expr): DiffNode = when {
        first == second -> DiffNode.Same(parent, selector)
        first.astKind != second.astKind -> DiffNode.Different(parent, selector)
        !first.isExpr -> DiffNode.Different(parent, selector)
        first.sort != second.sort -> DiffNode.Different(parent, selector)
        first.isApp && first.funcDecl != second.funcDecl -> DiffNode.Different(parent, selector)
        else -> {
            val node = DiffNode.Different(parent, selector)
            val firstNumArgs = max(0, first.numArgs)
            val secondNumArgs = max(0, first.numArgs)
            if (firstNumArgs != secondNumArgs) throw IllegalStateException("Same functions with different arguments number")
            for (argIndex in 0 until firstNumArgs) {
                val exprSelector = ExprSelector(argIndex)
                node.children += diff(node, exprSelector, exprSelector.get(first), exprSelector.get(second))
            }
            node
        }
    }
}

private data class ExprSelector(val argIndex: Int) {
    fun get(expr: Expr): Expr = when {
        argIndex >= expr.numArgs -> throw IllegalStateException("Unable to apply $this to $expr ")
        else -> expr.args[argIndex]
    }

    fun set(expr: Expr, value: Expr): Expr = when {
        argIndex >= expr.numArgs -> throw IllegalStateException("Unable to apply $this to $expr ")
        else -> {
            val args = expr.args
            args[argIndex] = value
            expr.update(args)
        }
    }
}

private data class DiffPath(val selectors: List<ExprSelector>) {
    fun eval(expr: Expr): Expr = selectors.fold(expr) { currExpr, selector -> selector.get(currExpr) }
    fun replaceAtPath(expr: Expr, newExpr: Expr): Expr {
        val pathElements = dequeOf(selectors)
        return replaceAtPath(expr, newExpr, pathElements)
    }

    private fun replaceAtPath(expr: Expr, newExpr: Expr, path: Deque<ExprSelector>): Expr = when {
        path.isEmpty() -> newExpr
        else -> {
            val current = path.removeFirst()
            current.set(expr, replaceAtPath(current.get(expr), newExpr, path))
        }
    }
}

private sealed class DiffNode(val parent: DiffNode?, val children: MutableList<DiffNode>, val selector: ExprSelector?) {
    val isTerminal: Boolean
        get() = children.isEmpty()

    class Same(parent: DiffNode?, selector: ExprSelector?) : DiffNode(parent, arrayListOf(), selector)
    class Different(parent: DiffNode?, selector: ExprSelector?) : DiffNode(parent, arrayListOf(), selector)

    fun path(): DiffPath {
        val path = arrayListOf<ExprSelector>()
        var node: DiffNode? = this
        while (node != null) {
            val selector = node.selector
            node = node.parent
            path += selector ?: continue
        }
        return DiffPath(path.reversed())
    }

    fun terminalNodes(): List<DiffNode> = when {
        isTerminal -> listOf(this)
        else -> children.flatMap { it.terminalNodes() }
    }
}

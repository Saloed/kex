package org.jetbrains.research.kex.smt.z3.expr

import com.abdullin.kthelper.collection.dequeOf
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import de.danielbechler.diff.NodeQueryService
import de.danielbechler.diff.ObjectDifferBuilder
import de.danielbechler.diff.access.Accessor
import de.danielbechler.diff.access.Instances
import de.danielbechler.diff.differ.Differ
import de.danielbechler.diff.differ.DifferDispatcher
import de.danielbechler.diff.node.DiffNode
import de.danielbechler.diff.node.Visit
import de.danielbechler.diff.selector.ElementSelector
import java.util.*
import kotlin.math.max

class FormulaDiffTool(val ctx: Context, val first: Expr, val second: Expr) : Z3ExpressionVisitor {
    fun diff(): Expr {
        val diff = exprDiffTool().compare<Expr>(first, second)
        val changed = ChangedNodesCollector.changedNodes(diff)
        var result = first
        for (change in changed) {
            result = applyChange(result, change)
        }
        return result
    }

    private fun applyChange(rootExpr: Expr, change: DiffNode): Expr {
        val path = change.path.elementSelectors.filterIsInstance<ExprArgElementSelector>()
        val pathElements = dequeOf(path)
        return applyChange(rootExpr, change, pathElements)
    }

    private fun applyChange(rootExpr: Expr, change: DiffNode, path: Deque<ExprArgElementSelector>): Expr {
        if (path.isEmpty()) {
            val firstExpr = change.canonicalGet(first) as? Expr ?: ctx.mkFreshConst("nothing", rootExpr.sort)
            val secondExpr = change.canonicalGet(second) as? Expr ?: ctx.mkFreshConst("nothing", rootExpr.sort)
            val diff = ctx.mkFreshFuncDecl("diff", arrayOf(firstExpr.sort, secondExpr.sort), rootExpr.sort)
            return ctx.mkApp(diff, firstExpr, secondExpr)
        }
        val current = path.removeFirst()
        val args = rootExpr.args
        val updated = applyChange(args[current.index], change, path)
        args[current.index] = updated
        return rootExpr.update(args)
    }

    companion object {
        private fun exprDiffTool() = ObjectDifferBuilder
                .startBuilding()
                .differs().register { dispatcher, nodeQueryService -> ExprDiffer(dispatcher, nodeQueryService) }
                .build()
    }
}

private class ExprDiffer(val dispatcher: DifferDispatcher, val nodeQueryService: NodeQueryService) : Differ {
    override fun accepts(type: Class<*>): Boolean = Expr::class.java.isAssignableFrom(type)
    override fun compare(parent: DiffNode?, instances: Instances): DiffNode {
        val node = DiffNode(parent, instances.sourceAccessor, instances.type)
        compareInstances(node, instances)
        return node
    }

    private fun compareInstances(node: DiffNode, instances: Instances) {
        val first = instances.base as Expr?
        val second = instances.working as Expr?
        when {
            first == null && second == null -> {
                node.state = DiffNode.State.UNTOUCHED
                return
            }
            first == null || second == null -> {
                node.state = DiffNode.State.CHANGED
                return
            }
            else -> compareExprs(node, first, second, instances)
        }
    }

    private fun compareExprs(node: DiffNode, first: Expr, second: Expr, instances: Instances) {
        when {
            first == second -> {
                node.state = DiffNode.State.UNTOUCHED
                return
            }
            first.astKind != second.astKind -> {
                node.state = DiffNode.State.CHANGED
                return
            }
            !first.isExpr -> {
                node.state = DiffNode.State.CHANGED
                return
            }
            first.sort != second.sort -> {
                node.state = DiffNode.State.CHANGED
                return
            }
            first.isApp && first.funcDecl != second.funcDecl -> {
                node.state = DiffNode.State.CHANGED
                return
            }
            else -> {
                val numArgs = max(0, max(first.numArgs, second.numArgs))
                if (numArgs == 0) {
                    node.state = DiffNode.State.CHANGED
                    return
                }
                for (argIndex in 0..numArgs) {
                    val child = dispatcher.dispatch(node, instances, ExprArgAccessor(argIndex))
                    node.addChild(child)
                }
            }
        }
    }
}

private interface ExprAccessor : Accessor {
    fun get(expr: Expr): Expr?
    fun set(expr: Expr, value: Expr?): Unit
    fun unset(expr: Expr): Unit

    override fun get(p0: Any?) = when (p0) {
        null -> null
        else -> get(p0 as Expr)
    }

    override fun set(p0: Any?, p1: Any?) = if (p0 != null) set(p0 as Expr, p1 as Expr?) else Unit
    override fun unset(p0: Any?) = if (p0 != null) unset(p0 as Expr) else Unit
}

private class ExprArgAccessor(val index: Int) : ExprAccessor {
    override fun get(expr: Expr): Expr? = when {
        index >= expr.numArgs -> null
        else -> expr.args[index]
    }

    override fun set(expr: Expr, value: Expr?): Unit = TODO("Not yet implemented")
    override fun unset(expr: Expr): Unit = TODO("Not yet implemented")
    override fun getElementSelector(): ElementSelector = ExprArgElementSelector(index)
}

private data class ExprArgElementSelector(val index: Int) : ElementSelector() {
    override fun toHumanReadableString(): String = "[$index]"
}

private class ChangedNodesCollector : DiffNode.Visitor {
    val nodes = arrayListOf<DiffNode>()
    override fun node(node: DiffNode, visit: Visit) {
        if (node.hasChanges() && !node.hasChildren()) nodes.add(node)
    }

    companion object {
        fun changedNodes(root: DiffNode) = ChangedNodesCollector().apply { root.visit(this) }.nodes
    }
}

package org.jetbrains.research.kex.util

import org.jetbrains.research.kthelper.collection.dequeOf
import java.util.*

abstract class DiffTool<T>(val first: T, val second: T) {
    open fun diff(): T {
        val diffNodes = diff(null, null, first, second).terminalNodes().filterIsInstance<DiffNode.Different<T>>()
        var result = first
        for (node in diffNodes) {
            val path = node.path()
            val firstExpr = path.eval(first)
            val secondExpr = path.eval(second)
            val diffApp = createDiffPlaceholder(firstExpr, secondExpr)
            result = path.replaceAtPath(result, diffApp)
        }
        return result
    }

    abstract fun diff(parent: DiffNode<T>?, selector: DiffSelector<T>?, first: T, second: T): DiffNode<T>
    abstract fun createDiffPlaceholder(left: T, right: T): T
}

interface DiffSelector<T> {
    fun get(expr: T): T
    fun set(expr: T, value: T): T
}

data class DiffPath<T>(val selectors: List<DiffSelector<T>>) {
    fun eval(expr: T): T = selectors.fold(expr) { currExpr, selector -> selector.get(currExpr) }
    fun replaceAtPath(expr: T, newExpr: T): T {
        val pathElements = dequeOf(selectors)
        return replaceAtPath(expr, newExpr, pathElements)
    }

    private fun replaceAtPath(expr: T, newExpr: T, path: Deque<DiffSelector<T>>): T = when {
        path.isEmpty() -> newExpr
        else -> {
            val current = path.removeFirst()
            current.set(expr, replaceAtPath(current.get(expr), newExpr, path))
        }
    }
}

sealed class DiffNode<T>(val parent: DiffNode<T>?, val children: MutableList<DiffNode<T>>, val selector: DiffSelector<T>?) {
    private val isTerminal: Boolean
        get() = children.isEmpty()

    class Same<T>(parent: DiffNode<T>?, selector: DiffSelector<T>?) : DiffNode<T>(parent, arrayListOf(), selector)
    class Different<T>(parent: DiffNode<T>?, selector: DiffSelector<T>?) : DiffNode<T>(parent, arrayListOf(), selector)

    fun path(): DiffPath<T> {
        val path = arrayListOf<DiffSelector<T>>()
        var node: DiffNode<T>? = this
        while (node != null) {
            val selector = node.selector
            node = node.parent
            path += selector ?: continue
        }
        return DiffPath(path.reversed())
    }

    fun terminalNodes(): List<DiffNode<T>> = when {
        isTerminal -> listOf(this)
        else -> children.flatMap { it.terminalNodes() }
    }
}
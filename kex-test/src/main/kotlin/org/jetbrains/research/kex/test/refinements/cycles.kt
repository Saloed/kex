package org.jetbrains.research.kex.test.refinements

object Cycles {
    data class XCls(var clsFieldA: Int, var clsFieldB: Int)

    fun cycle(first: XCls, arg: Int): Int {
        for (i in 0..arg) {
            first.clsFieldA += 1
        }
        if (first.clsFieldA == first.clsFieldB) {
            throw IllegalArgumentException("Bad argument")
        }
        return 0
    }

    fun <T : Comparable<T>> max(x: T, y: T) = if (y > x) y else x

    fun arrayMax(array: IntArray, size: Int): Int {
        var currentMax = array.first()
        for (i in 0..size) {
            currentMax = max(currentMax, array[i])
        }
        return currentMax
    }

}
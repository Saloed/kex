package org.jetbrains.research.kex.test.refinements

object Classes {

    data class XCls(var clsFieldA: Int, var clsFieldB: Int)
    data class YCls(var clsFieldA: Int, var clsFieldB: Int)

    fun mutablePropertyAndLocalObject(first: XCls, arg: Int): Int {
        val second = XCls(arg, 123132)
        first.clsFieldA += 2
        if (first.clsFieldA == second.clsFieldA) {
            throw IllegalArgumentException("first A equal to second A")
        }
        if (first.clsFieldA > second.clsFieldA) {
            return 0
        }
        return first.clsFieldA + second.clsFieldB
    }

    fun mutablePropertyAndLocalObjectSmall(first: XCls, arg: Int): Int {
        val second = XCls(123132, arg)
        first.clsFieldB += 2
        if (first.clsFieldB == second.clsFieldB) {
            throw IllegalArgumentException("first B equal to second B")
        }
        return 0
    }

    fun mutableProperty(first: XCls, arg: Int): Int {
        first.clsFieldA += 2
        if (first.clsFieldA == arg) {
            throw IllegalArgumentException("first A equal to arg")
        }
        return 0
    }

    fun manyClassArgs(first: XCls, second: XCls, third: XCls): Int {
        first.clsFieldB += second.clsFieldB
        third.clsFieldB += 10

        when {
            first.clsFieldB == second.clsFieldB -> throw IllegalArgumentException("First eq second")
            second.clsFieldB == third.clsFieldB -> throw IllegalArgumentException("Second eq third")
            first.clsFieldB == third.clsFieldB -> throw IllegalArgumentException("First eq third")
            else -> return 0
        }
    }

    fun unusedArgs(first: XCls, second: XCls): Int {
        if (first.clsFieldB > 0) {
            throw IllegalArgumentException("Bad argument")
        }
        return second.clsFieldA
    }

    fun intMax(a: Int, b: Int) = if (a >= b) a else b

    fun complex(first: XCls, second: XCls, xx: Int): Int {
        val maxA = intMax(first.clsFieldA, second.clsFieldA)
        val maxB = intMax(first.clsFieldB, second.clsFieldB)
        val maxCls = YCls(maxA, maxB)
        maxCls.clsFieldA += first.clsFieldA
        maxCls.clsFieldB += first.clsFieldB
        if (xx < 0) {
            throw IllegalArgumentException("Something wrong")
        }
        if (maxCls.clsFieldA < maxCls.clsFieldB) {
            throw IllegalStateException("Something wrong 2")
        }
        return maxA + maxB
    }
}
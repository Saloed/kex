package org.jetbrains.research.kex.test.refinements

object Recursive {
    data class XCls(var clsFieldA: Int, var clsFieldB: Int)

    fun isPositive(i: Int) {
        if (i < 0) throw IllegalArgumentException("Not positive")
    }

    fun isGreater(i: Int, constant: Int) {
        if (i < constant) throw IllegalArgumentException("Lower then constant")
    }

    fun recursiveSimple(a: Int, b: Int): Int {
        if (a < 0) throw IllegalArgumentException("A is not positive")
        if (b < 0) throw IllegalArgumentException("B is not positive")

        val res = when {
            a < b -> a
            a > b -> recursiveSimple(a - 1, b)
            else -> recursiveSimple(a - 1, b - 2)
        }

        if (res < 17) throw IllegalArgumentException("Res is not ok")
        return res
    }

    fun recursiveWithNestedCalls(a: Int, b: Int): Int {
        isPositive(a)
        isPositive(b)

        val res = when {
            a < b -> a
            a > b -> recursiveWithNestedCalls(a - 1, b)
            else -> recursiveWithNestedCalls(a - 1, b - 2)
        }
        isGreater(res, 17)
        return res
    }


    fun recursiveAlwaysException(a: Int): Int {
        if (a < 0) throw IllegalArgumentException("A is not positive")
        val res = when {
            a == 0 -> a
            else -> recursiveAlwaysException(a - 1)
        }
        isGreater(res, 17)
        return res
    }

    fun recursiveWithStackOverflow(a: Int): Int {
        if (a == 0) return 0
        return recursiveWithStackOverflow(a + 1)
    }

    fun recursiveFunctionCall(a: Int, b: Int): Int {
        if (a <= 100) {
            throw IllegalArgumentException("A must be grater then 100")
        }
        return recursiveSimple(a, b)
    }

    fun recursiveWithMemory(x: XCls, y: XCls): Int {
        if (x.clsFieldA < 0 || x.clsFieldB < 0) throw IllegalArgumentException("A is not positive")
        if (y.clsFieldB < 0 || y.clsFieldA < 0) throw IllegalArgumentException("B is not positive")

        val res = when {
            x.clsFieldA < y.clsFieldB -> x.clsFieldA
            x.clsFieldA > y.clsFieldB -> {
                x.clsFieldA -= 1
                recursiveWithMemory(x, y)
            }
            else -> {
                x.clsFieldA -= 1
                y.clsFieldB -= 2
                recursiveWithMemory(x, y)
            }
        }
        if (res < 17) throw IllegalArgumentException("Res is not ok")
        return res
    }

}
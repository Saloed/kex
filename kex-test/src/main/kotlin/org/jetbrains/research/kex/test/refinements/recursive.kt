package org.jetbrains.research.kex.test.refinements

object Recursive {
    data class XCls(var clsFieldA: Int, var clsFieldB: Int)
    data class ImmutableIntWrapper(val value: Int)
    data class MutableIntWrapper(var value: Int)

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

    fun recursiveSimpleTail(x: Int): Int {
        if (x > 100) return x
        val tmp = x + 5
        if (tmp <= 17) throw IllegalArgumentException("Ex")
        return recursiveSimpleTail(tmp + 1)
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

    fun simpleRecursionWithImmutableMemory(x: ImmutableIntWrapper, y: Int): Int = when {
        y < 0 -> throw IllegalStateException("Stop iteration")
        y == 0 -> 1
        else -> {
            if (x.value >= 20) throw IllegalStateException("Overflow")
            val xCopy = ImmutableIntWrapper(x.value + 1)
            simpleRecursionWithImmutableMemory(xCopy, y - 1)
        }
    }

    fun simpleRecursionWithMutableMemory(x: MutableIntWrapper, y: Int): Int = when {
        y < 0 -> throw IllegalStateException("Stop iteration")
        y == 0 -> 1
        else -> {
            if (x.value >= 20) throw IllegalStateException("Overflow")
            x.value += 1
            simpleRecursionWithMutableMemory(x, y - 1)
        }
    }

    fun mutableMemoryOnlyClsArg(x: MutableIntWrapper): Int {
        if (x.value < 0) throw IllegalStateException("1")
        if (x.value == 17) throw IllegalStateException("2")
        if (x.value > 100) return 0
        x.value += 1
        return mutableMemoryOnlyClsArg(x)
    }

    fun mutableMemoryDependency(x: MutableIntWrapper, depth: Int): Int {
        x.value -= 1
        if (x.value < 0) return 0
        if (depth > 100) return 1
        mutableMemoryDependency(x, depth + 1)
        if (x.value != 0) throw IllegalStateException("2")
        return 0
    }

    fun mutableMemoryDependencyCounter(x: MutableIntWrapper): Int {
        if (x.value > 100) return 100
        val valueBefore = x.value
        x.value += 1
        mutableMemoryDependencyCounter(x)
        x.value -= 1
        if (x.value != valueBefore) throw IllegalStateException("Counter failed")
        return 0
    }

    fun mutableMemoryDependencyCounterWithDepth(x: MutableIntWrapper, depth: Int): Int {
        if (depth <= 0) return 0
        x.value += 1
        mutableMemoryDependencyCounterWithDepth(x, depth - 1)
        if (x.value == 17) throw IllegalStateException("Counter failed")
        return 0
    }

    fun preventFromInlining() {}

    fun someNonRecursiveFunction(x: MutableIntWrapper): Int {
        preventFromInlining()
        if (x.value > 17) {
            throw IllegalArgumentException("Bad argument")
        }
        val oldValue = x.value
        x.value += 3
        return oldValue
    }

    fun recursiveWithFunctionCalls(x: MutableIntWrapper): Int {
        x.value += 2
        if (x.value > 19) return 0
        val oldX = someNonRecursiveFunction(x)
        if (oldX == 15) throw IllegalArgumentException("More exceptions")
        return recursiveWithFunctionCalls(x)
    }

    fun simpleNonRecursiveFunction(a: Int): Int {
        preventFromInlining()
        return a + 5
    }

    fun recursiveWithFunctionCallsSimple(x: Int): Int {
        if (x > 100) return x
        val tmp = simpleNonRecursiveFunction(x)
        if (tmp <= 17) throw IllegalArgumentException("Ex")
        return recursiveWithFunctionCallsSimple(tmp + 1)
    }

}


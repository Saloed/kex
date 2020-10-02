package org.jetbrains.research.kex.test.refinements

object Simple {

    fun simpleNoReturn(a: Int) {
        if (a <= 0) {
            throw IllegalArgumentException("A must be grater then zero")
        }
    }

    fun simpleWithReturn(a: Int): String {
        if (a <= 0) {
            throw IllegalArgumentException("A must be grater then zero")
        }
        return ""
    }

    fun simpleUnusedUnknown(x: Int): Int {
        if (x < 0) {
            throw IllegalArgumentException("X must be grater then or equals zero")
        }
        val a = ""
        if (a.isEmpty()) {
            return 17
        }
        return a.length
    }

    fun simpleNestedCall(x: Int): Int {
        if (x < 0) {
            throw IllegalArgumentException("X must be grater then or equals zero")
        }
        val a = simpleWithReturn(x)
        return a.length
    }

    fun simpleNestedCallAndUnusedUnknown(x: Int): Int {
        if (x < 0) {
            throw IllegalArgumentException("X must be grater then or equals zero")
        }
        val a = simpleWithReturn(x)
        if (a.isEmpty()) {
            return 17
        }
        return a.length
    }


    fun compare(a: Int, b: Int): Int {
        if (a == b) throw IllegalArgumentException("A eq B")
        if (a < b) {
            return -1
        } else {
            return 1
        }
    }

    fun simpleExceptionOnNestedCallResult(x: Int): Int {
        val test = compare(x, 17)
        if (test < 0) throw IllegalArgumentException("Test lt 0")
        return test * x
    }

    fun floatsAndDoubles(a: Float, b: Double): Int {
        val x = a + 1 - b
        if (x != 2.0) throw IllegalArgumentException("")
        return 0
    }

    fun forceValue(a: Int) = a

    fun simpleManyExceptionSources(a: Int): Int {
        val x = if (a > 0) throw IllegalStateException("exception") else 17
        forceValue(x)
        if (x == 17 && a < 0) throw IllegalStateException("bad result")
        return 0
    }

    fun alwaysException(): Int = throw IllegalStateException("Exception")

    fun shadowedExceptions(x: Int): Int {
        val a = if (x > 0) 1 else 0
        throw IllegalStateException("Exception")
        val b = a + 1
        throw IllegalArgumentException("Shadowed")
    }

    fun shadowedExceptionWithCall(x: Int): Int {
        val a = if (x > 0) 1 else 0
        alwaysException()
        val b = a + 1
        throw IllegalArgumentException("Shadowed")
    }
}

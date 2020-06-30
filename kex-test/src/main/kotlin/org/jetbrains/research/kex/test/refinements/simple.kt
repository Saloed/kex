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

}

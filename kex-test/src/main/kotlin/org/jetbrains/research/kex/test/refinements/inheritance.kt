package org.jetbrains.research.kex.test.refinements

object Inheritance {
    interface Checker {
        fun check(a: Int): Int
    }

    class PositiveCheck : Checker {
        override fun check(a: Int): Int {
            if (a > 0) throw IllegalArgumentException("Positive check")
            return a
        }
    }

    class NegativeCheck : Checker {
        override fun check(a: Int): Int {
            if (a < 0) throw IllegalArgumentException("Negative check")
            return a
        }
    }

    fun interfaceInlining(checker: Checker, x: Int): Int {
        val res = checker.check(x)
        if (res == 0) throw IllegalArgumentException("Zero")
        return res
    }

}
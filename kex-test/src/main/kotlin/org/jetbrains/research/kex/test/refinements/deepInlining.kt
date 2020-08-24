package org.jetbrains.research.kex.test.refinements

object DeepInlining {

    open class ExceptionalBase(val a: Int) {
        init {
            if (a < 0) throw IllegalStateException("a below zero")
        }
    }

    open class ExceptionalClass(val b: Int, a: Int) : ExceptionalBase(a) {
        init {
            if (b < a) throw IllegalArgumentException("b lt a")
        }
    }

    class SomeClass(val x: Int, b: Int, a: Int) : ExceptionalClass(b, a)


    fun simplyInlineableMethod(x: Int): Int {
        if (x < 0) throw IllegalStateException("x below zero")
        return 0
    }

    fun nonSimplyInlineableMethod(b: Int): Int {
        if (b > 100) throw IllegalStateException("b over 100")
        return simplyInlineableMethod(b)
    }

    fun deepInlineTest(a: Int, b: Int, x: Int): Int {
        val cls = SomeClass(x, b, a)
        simplyInlineableMethod(cls.x)
        nonSimplyInlineableMethod(cls.b)
        return 0
    }

}
package org.jetbrains.research.kex.test.refinements

object Inlining {

    data class IntBox(val value: Int) {
        inline fun transform(fn: (Int) -> Int) = IntBox(fn(value))
    }

    fun deepInlining(a: Int): Int {
        val box = IntBox(a)
        val res = inlineLvl1(box)
        if (res.value == 0) throw IllegalArgumentException("Zero")
        return res.value
    }

    private fun inlineLvl1(x: IntBox): IntBox {
        return inlineLvl2(x.transform { it + 1 }).transform { it + 1 }
    }

    private fun inlineLvl2(x: IntBox): IntBox {
        return inlineLvl3(x.transform { it + 2 }).transform { it + 2 }
    }

    private fun inlineLvl3(x: IntBox): IntBox {
        if (x.value < 0) throw IllegalArgumentException("Below zero")
        return x.transform { it + 1 }
    }

    class Failer {
        fun exceptionSource(a: Int): Nothing {
            throw IllegalStateException("failed")
        }
    }

    fun inlineExceptionSource(f: Failer, x: Int): Nothing {
        var a = 17
        if (x != 0) {
            a += 5
        }
        f.exceptionSource(a)
    }


    data class SampleCls(val x: Int)

    fun process1(arg: SampleCls): SampleCls {
        return arg
    }

    fun process2(arg: SampleCls): SampleCls {
        return SampleCls(5)
    }

    fun process3(arg: SampleCls): SampleCls {
        return SampleCls(arg.x + 1)
    }

    fun sample(a: Int, b: SampleCls): SampleCls {
        val result = when {
            a > b.x -> process1(b)
            else -> process2(b)
        }
        val updatedResult = process3(result)
        if (updatedResult.x < a) throw IllegalStateException()
        return result
    }

    fun exceptionSource(a: Int): Boolean {
        if (a > 0) throw IllegalStateException("exception")
        return true
    }

    fun inlineWithResultDependency(a: Int): Int {
        val x = exceptionSource(a)
        if (x && a < 0) throw IllegalStateException("bad result")
        return 0
    }

    fun exceptionSource2(a: Int): Int {
        if (a > 0) throw IllegalStateException("Positive check")
        return a
    }

    fun inlineWithResultDependency2(x: Int): Int {
        val res = exceptionSource2(x)
        if (res == 0) throw IllegalStateException("Zero")
        return res
    }

    fun inlineWithoutResultDependency(a: Int): Int{
        exceptionSource(a)
        if (a < 0) throw IllegalStateException("bad result")
        return 0
    }
}

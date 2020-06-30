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

}
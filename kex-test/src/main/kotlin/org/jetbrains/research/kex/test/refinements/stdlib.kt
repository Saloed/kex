package org.jetbrains.research.kex.test.refinements

object Stdlib {
    fun unsafeFirstInt(x: List<Int>): Int {
        return x.first()
    }

    fun unsafeFirstStr(x: List<String>): String {
        return x.first()
    }

    fun unsafeFirstBool(x: List<Boolean>): Boolean {
        return x.first()
    }
}
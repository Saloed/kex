package org.jetbrains.research.kex.test.refinements

object Unknowns {
    fun unknownSimple(a: Int): Int {
        if (listOf(a).isNotEmpty()) {
            throw IllegalStateException("Why not?")
        }
        return a
    }

    fun unknownFunctionCall(x: Int): Int {
        val tmp = unknownSimple(x)
        if (tmp < 0) throw IllegalStateException("Below zero")
        return -tmp
    }

    fun recursiveUnknownFunction(x: List<Int>): Int {
        if (x.size == 100) throw IllegalArgumentException("List is full")
        if (x.first() == 99) return x.first()
        return recursiveUnknownFunction(x + x.size)
    }
}
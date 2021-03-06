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

    interface MyList<T> {
        fun isEmpty(): Boolean
        fun get(idx: Int): T
    }

    private fun <T> MyList<T>.first(): T {
        if (isEmpty()) throw IllegalArgumentException("Empty")
        return get(0)
    }

    fun unknownInterfaceMethods(x: MyList<String>): String {
        return x.first()
    }

}
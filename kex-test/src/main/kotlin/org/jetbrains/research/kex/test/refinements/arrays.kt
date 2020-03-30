package org.jetbrains.research.kex.test.refinements

object Arrays {
    fun arrayTest(array: IntArray, i: Int): Int {
        if (i < 0 || i >= array.size) {
            throw ArrayIndexOutOfBoundsException("out of bounds")
        }
        if (array[i] < 0) {
            throw IllegalArgumentException("Indexed must be positive")
        }
        return array[i]
    }
}
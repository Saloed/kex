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

    fun arrayTest2(a1: IntArray, a2: DoubleArray, a3: Array<Any>, i: Int){
        if(a1[i] == a2[i].toInt() && a1[i] == a3[i]){
            throw IllegalArgumentException("Aaaaaa")
        }
    }
}

package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.Context
import com.microsoft.z3.IntSort

open class ContextWithIntSortSizeInfo : Context() {
    val intSortSize = hashMapOf<IntSort, Int>()
}

fun createContext() = ContextWithIntSortSizeInfo()

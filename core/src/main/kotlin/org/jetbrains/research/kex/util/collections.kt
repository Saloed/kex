package org.jetbrains.research.kex.util

fun <T> List<T>.join(combiner: (T, T) -> T) = when(size){
    0 -> throw IllegalStateException("Nothing to join")
    1 -> first()
    else -> drop(1).fold(first(), combiner)
}

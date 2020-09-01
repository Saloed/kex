package org.jetbrains.research.kex.state.memory

object MemoryVersionComparator : Comparator<MemoryVersion> {
    override fun compare(left: MemoryVersion, right: MemoryVersion): Int {
        val leftGeRight = left.dependsOn(right)
        val rightGeLeft = right.dependsOn(left)
        return when {
            leftGeRight && !rightGeLeft -> 1
            rightGeLeft && !leftGeRight -> -1
            else -> 0
        }
    }
}

internal fun MemoryVersion.dependsOn(other: MemoryVersion): Boolean = when (other) {
    this -> true
    else -> predecessors.any { it.dependsOn(other) }
}

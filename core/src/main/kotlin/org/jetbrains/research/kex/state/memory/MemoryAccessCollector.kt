package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.PredicateState

internal class MemoryAccessCollector private constructor() : MemoryVersionTransformer {
    private val memoryAccesses = arrayListOf<MemoryAccess<*>>()
    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        memoryAccesses += element
        return super.transformMemoryVersion(element)
    }

    companion object {
        fun collect(ps: PredicateState) = MemoryAccessCollector().apply { apply(ps) }.memoryAccesses
    }
}
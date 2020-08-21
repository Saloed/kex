package org.jetbrains.research.kex.state.memory

internal class ScopeInfoMapper(val mapping: Map<MemoryDescriptor, MemoryAccessScope>) : MemoryVersionTransformer{
    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val newScope = mapping[element.descriptor()] ?: error("No scope mapped for element ${element.descriptor()}")
        return element.withScopeInfo(newScope)
    }
}
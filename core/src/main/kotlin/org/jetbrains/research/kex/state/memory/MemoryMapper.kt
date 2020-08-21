package org.jetbrains.research.kex.state.memory

internal class MemoryMapper(val mapping: MemoryMappingType) : MemoryVersionTransformer {
    @Suppress("UNCHECKED_CAST")
    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val currentDescriptor = element.descriptor()
        val elementKey = currentDescriptor to element.memoryVersion
        val (newDescriptor, newVersion) = mapping[elementKey] ?: return super.transformMemoryVersion(element)
        check(currentDescriptor.run {
            memoryType == newDescriptor.memoryType
                    && memoryName == newDescriptor.memoryName
                    && memorySpace == newDescriptor.memorySpace
        }) { "This mapper can change only scope info" }
        var result = element.withScopeInfo(newDescriptor.scopeInfo)
        result as MemoryAccess<T>
        result = result.withMemoryVersion(newVersion)
        return result
    }
}

package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.PredicateState

typealias MemoryMappingType = Map<Pair<MemoryDescriptor, MemoryVersion>, Pair<MemoryDescriptor, MemoryVersion>>

internal class MemoryNewAsInitial {
    fun newAsSeparateInitialVersions(state: PredicateState): Pair<PredicateState, MemoryMappingType> {
        val calls = MemoryUtils.collectCallMemory(state)
        check(calls.isEmpty()) { "Translating new to separate initials is not supported for calls" }
        val memoryAccess = MemoryUtils.collectMemoryAccesses(state).groupBy { it.descriptor() }
        val mapping = memoryAccess.flatMap { (descriptor, access) ->
            check(access.map { it.memoryVersion.type }.all { it in listOf(MemoryVersionType.INITIAL, MemoryVersionType.NEW, MemoryVersionType.NORMAL) }) { "Unsupported memory type" }
            val groupedByMajor = access.groupBy { it.memoryVersion.version }
            groupedByMajor.flatMap { newAsSeparateInitialVersions(descriptor, it.value).entries }
        }.associateBy({ it.key }, { it.value })
        val mapper = DescriptorMapper(mapping)
        val result = mapper.apply(state)
        return result to mapper.resultMapping
    }

    private fun newAsSeparateInitialVersions(descriptor: MemoryDescriptor, access: List<MemoryAccess<*>>): Map<Pair<MemoryDescriptor, MemoryVersion>, Pair<MemoryAccessScope, MemoryVersion>> {
        val memories = access.associateBy { it.memoryVersion }
        val root = memories.keys.first { it.type == MemoryVersionType.INITIAL || it.type == MemoryVersionType.NEW }
        val dependencyTree = hashMapOf<MemoryVersion, MutableSet<MemoryVersion>>()
        for (version in memories.keys) {
            if (version == root) continue
            version.predecessors.map { dependencyTree.getOrPut(it) { hashSetOf() } += version }
        }
        check((dependencyTree.keys - memories.keys).isEmpty()) { "Dependency tre is not closed" }

        if (dependencyTree.isEmpty()) {
            val newScope = descriptor.scopeInfo.withScope(root.machineName)
            return mapOf(descriptor to root to (newScope to MemoryVersion.initial()))
        }
        TODO()
    }

    @Suppress("UNCHECKED_CAST")
    private class DescriptorMapper(val mapping: Map<Pair<MemoryDescriptor, MemoryVersion>, Pair<MemoryAccessScope, MemoryVersion>>) : MemoryVersionTransformer {
        val resultMapping = hashMapOf<Pair<MemoryDescriptor, MemoryVersion>, Pair<MemoryDescriptor, MemoryVersion>>()
        override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
            val elementKey = element.descriptor() to element.memoryVersion
            val (newScope, newVersion) = mapping[elementKey] ?: return super.transformMemoryVersion(element)
            var result = element.withScopeInfo(newScope)
            result as MemoryAccess<T>
            result = result.withMemoryVersion(newVersion)
            result as MemoryAccess<T>
            val newElementValue = result.descriptor() to result.memoryVersion
            resultMapping[elementKey] = newElementValue
            return result
        }
    }
}

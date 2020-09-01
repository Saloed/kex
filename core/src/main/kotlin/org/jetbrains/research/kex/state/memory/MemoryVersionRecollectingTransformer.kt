package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.PredicateState

class RecollectingMemoryState(
        val mapping: Map<MemoryDescriptor, MutableMap<MemoryVersion, MemoryVersion>>,
        memory: Map<MemoryDescriptor, MemoryVersion>
) : MemoryState(memory) {
    override fun write(descriptor: MemoryDescriptor, memoryVersion: MemoryVersion): MemoryState {
        val current = memory.getValue(descriptor)
        val newVersion = current.increaseSubversion().transformMapped(descriptor, current) { it.increaseSubversion() }
        val newMemory = memory.plus(descriptor to newVersion)
        return RecollectingMemoryState(mapping, newMemory)
    }

    override fun reset(version: Int): MemoryState {
        val newMemory = memory.mapValues { (descriptor, currentVersion) ->
            currentVersion.resetToVersion(version).transformMapped(descriptor, currentVersion) { it.resetToVersion(version) }
        }
        return RecollectingMemoryState(mapping, newMemory)
    }

    override fun merge(others: List<MemoryState>): MemoryState {
        val newMemory = memory.mapValues { (descriptor, defaultMemory) ->
            val alternatives = others.map { it.memory.getValue(descriptor) }
            val newVersion = MemoryVersion.merge(listOf(defaultMemory) + alternatives)
            val descriptorMapping = mapping.getValue(descriptor)
            val defaultMapping = descriptorMapping[defaultMemory]
                    ?: error("No version mapped")
            val alternativesMapping = alternatives.map {
                descriptorMapping[it] ?: error("No version mapped")
            }
            val mappedVersion = MemoryVersion.merge(listOf(defaultMapping) + alternativesMapping)
            descriptorMapping[newVersion] = mappedVersion
            newVersion
        }
        return RecollectingMemoryState(mapping, newMemory)
    }

    private fun MemoryVersion.transformMapped(
            descriptor: MemoryDescriptor,
            version: MemoryVersion,
            transformation: (MemoryVersion) -> MemoryVersion
    ): MemoryVersion {
        val descriptorMapping = mapping.getValue(descriptor)
        val mapped = descriptorMapping[version]
                ?: error("No version mapped")
        val newMapped = transformation(mapped)
        descriptorMapping[this] = newMapped
        return this
    }

    override fun create(state: MemoryState) = RecollectingMemoryState(mapping, state.memory)
}

open class MemoryVersionRecollectingTransformer : MemorySimulator() {
    override fun apply(ps: PredicateState): PredicateState {
        val descriptors = MemoryUtils.collectMemoryAccesses(ps).map { it.descriptor() }.distinct()
        val initialMemory = descriptors.associateWith { MemoryVersion.initial() }
        val mapping = initialMemory.mapValues { (_, version) -> hashMapOf(version to version) }
        val finalState = apply(ps, RecollectingMemoryState(mapping, initialMemory))
        return applyMapping(ps, finalState)
    }

    open fun applyMapping(state: PredicateState, recollectedState: RecollectingMemoryState): PredicateState{
        return StrictMemoryVersionMapper(recollectedState.mapping).apply(state)
    }

    open fun apply(state: PredicateState, recollectingState: RecollectingMemoryState): RecollectingMemoryState {
        memoryState = recollectingState
        super.apply(state)
        return memoryState
    }

    var memoryState: RecollectingMemoryState
        get() = memory as RecollectingMemoryState
        set(value) {
            memory = value
        }
}

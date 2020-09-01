package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.PredicateState

internal class MemoryVersionVerificationState(
        private val memoryInfo: Map<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>,
        memory: Map<MemoryDescriptor, MemoryVersion>
) : MemoryState(memory) {
    override fun read(descriptor: MemoryDescriptor, memoryVersion: MemoryVersion): MemoryState {
        val possibleVersions = memoryInfo.getValue(descriptor)
        check(memoryVersion in possibleVersions) { "Unexpected memory version $memoryVersion" }
        return super.read(descriptor, memoryVersion)
    }
    override fun write(descriptor: MemoryDescriptor, memoryVersion: MemoryVersion): MemoryState {
        val newVersion = memory.getValue(descriptor).increaseSubversion()
        val possibleVersions = memoryInfo.getValue(descriptor)
        check(memoryVersion in possibleVersions) { "Unexpected memory version $memoryVersion" }
        check(newVersion in possibleVersions) { "Unexpected memory version $newVersion" }
        check(newVersion == memoryVersion.increaseSubversion()) { "Incorrect version after write" }
        return super.write(descriptor, memoryVersion)
    }

    override fun reset(version: Int): MemoryState {
        val newMemory = super.reset(version)
        newMemory.memory.forEach { (descriptor, version) ->
            val possibleVersions = memoryInfo.getValue(descriptor)
            check(version in possibleVersions) { "Unexpected memory version $version" }
        }
        return newMemory
    }

    override fun merge(others: List<MemoryState>): MemoryState {
        val newMemory = super.merge(others)
        newMemory.memory.forEach { (descriptor, version) ->
            val possibleVersions = memoryInfo.getValue(descriptor)
            check(version in possibleVersions) { "Unexpected memory version $version" }
        }
        return newMemory
    }

    override fun create(state: MemoryState) = MemoryVersionVerificationState(memoryInfo, state.memory)
}

object MemoryVersionInfoVerifier {
    fun verify(state: PredicateState, memoryInfo: MemoryVersionInfo) {
        val initial = MemoryVersionVerificationState(memoryInfo.allMemoryVersions, memoryInfo.initial)
        val verifier = MemorySimulator(initial)
        verifier.apply(state)
        val finalState = verifier.memory
        check(finalState.memory == memoryInfo.final) { "Incorrect final memory" }
    }
}

package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.PredicateState

object MemoryVersionInfoCollector {
    fun collect(state: PredicateState): MemoryVersionInfo {
        val descriptors = MemoryUtils.collectMemoryAccesses(state).map { it.descriptor() }.distinct()
        val initialState = MemoryState(descriptors.associateWith { MemoryVersion.initial() })
        val simulator = MemorySimulator(initialState)
        simulator.apply(state)
        val finalState = simulator.memory
        return MemoryVersionInfo(initialState.memory, finalState.memory)
    }
}

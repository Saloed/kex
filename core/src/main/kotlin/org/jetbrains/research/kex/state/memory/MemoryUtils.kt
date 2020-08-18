package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector

object MemoryUtils {
    fun allVersionsUpToRoot(version: MemoryVersion): Set<MemoryVersion> = setOf(version) + version.predecessors.flatMap { allVersionsUpToRoot(it) }.toSet()
    fun verifyVersions(ps: PredicateState) {
        VersionVerifier.apply(ps)
    }

    fun view(ps: PredicateState) = MemoryVersionViewer.view(ps)
    fun collectMemoryAccesses(ps: PredicateState) = MemoryAccessCollector.collect(ps)
    fun collectCallMemory(ps: PredicateState) = PredicateCollector.collectIsInstance<CallPredicate>(ps)
            .flatMap { memoryVersionDescendantTree(it.memoryVersion).entries }
            .groupBy { it.key }
            .mapValues { it.value.flatMap { it.value }.toSet() }

    fun initializeMemoryVersionsAndPrepareForReplacement(state: PredicateState, replacementState: PredicateState, replaceVersion: MemoryVersion) = MemoryVersionReplacer(state, replaceVersion, replacementState).replace()

    fun memoryVersionDescendantTree(memoryAccess: List<MemoryAccess<*>>): Map<MemoryDescriptor, Map<MemoryVersion, Set<MemoryVersion>>> {
        val memoryDependency = hashMapOf<MemoryDescriptor, MutableMap<MemoryVersion, MutableSet<MemoryVersion>>>()
        memoryAccess.forEach { memory ->
            val dependencyData = memoryDependency.getOrPut(memory.descriptor()) { hashMapOf() }
            updateMemoryVersionDescendantTree(dependencyData, memory.memoryVersion)
        }
        return memoryDependency
    }

    fun memoryVersionDescendantTree(memoryVersion: MemoryVersion): Map<MemoryVersion, Set<MemoryVersion>> {
        val dependencyData = hashMapOf<MemoryVersion, MutableSet<MemoryVersion>>()
        updateMemoryVersionDescendantTree(dependencyData, memoryVersion)
        return dependencyData
    }

    private fun updateMemoryVersionDescendantTree(dependencyData: MutableMap<MemoryVersion, MutableSet<MemoryVersion>>, version: MemoryVersion) {
        version.predecessors.forEach { dependencyData.getOrPut(it) { hashSetOf() } += version }
        version.predecessors.forEach { updateMemoryVersionDescendantTree(dependencyData, it) }
    }

    fun newAsSeparateInitialVersions(state: PredicateState) = MemoryNewAsInitial().newAsSeparateInitialVersions(state)
}
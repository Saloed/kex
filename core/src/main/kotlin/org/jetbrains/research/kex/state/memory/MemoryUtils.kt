package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector

object MemoryUtils {
    fun verifyVersions(ps: PredicateState) {
        VersionVerifier.apply(ps)
    }

    fun verify(ps: PredicateState, memoryVersionInfo: MemoryVersionInfo){
        VersionVerifier.apply(ps)
        MemoryVersionInfoVerifier.verify(ps, memoryVersionInfo)
    }

    fun view(ps: PredicateState) = MemoryVersionViewer.view(ps)
    fun collectMemoryAccesses(ps: PredicateState) = MemoryAccessCollector.collect(ps)
    fun collectCallMemory(ps: PredicateState) = PredicateCollector.collectIsInstance<CallPredicate>(ps)
            .flatMap { memoryVersionDescendantTree(it.memoryVersion).entries }
            .groupBy { it.key }
            .mapValues { it.value.flatMap { it.value }.toSet() }

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

    fun mergeMemoryVersionTrees(
            left: Map<MemoryDescriptor, Map<MemoryVersion, Set<MemoryVersion>>>,
            right: Map<MemoryDescriptor, Map<MemoryVersion, Set<MemoryVersion>>>
    ) = (left.keys + right.keys).associateWith { mergeMemoryVersionTrees(it, left, right) }

    private fun mergeMemoryVersionTrees(
            descriptor: MemoryDescriptor,
            left: Map<MemoryDescriptor, Map<MemoryVersion, Set<MemoryVersion>>>,
            right: Map<MemoryDescriptor, Map<MemoryVersion, Set<MemoryVersion>>>
    ): Map<MemoryVersion, Set<MemoryVersion>> {
        val lhs = left[descriptor] ?: return right.getValue(descriptor)
        val rhs = right[descriptor] ?: return lhs
        val mergeResult = lhs.mapValues { it.value.toMutableSet() }.toMutableMap()
        rhs.flatMap { it.value + it.key }.forEach { updateMemoryVersionDescendantTree(mergeResult, it) }
        return mergeResult
    }

    private fun updateMemoryVersionDescendantTree(dependencyData: MutableMap<MemoryVersion, MutableSet<MemoryVersion>>, version: MemoryVersion) {
        version.predecessors.forEach { dependencyData.getOrPut(it) { hashSetOf() } += version }
        version.predecessors.forEach { updateMemoryVersionDescendantTree(dependencyData, it) }
    }

    fun newAsSeparateInitialVersions(state: PredicateState) = MemoryNewAsInitial().newAsSeparateInitialVersions(state)
    fun replaceMemoryVersion(state: PredicateState, from: MemoryVersion, to: MemoryVersion) = MemoryVersionReplacer.replace(state, from, to)
    fun replaceMemoryVersion(state: PredicateState, replacement: Map<MemoryDescriptor, Pair<MemoryVersion, MemoryVersion>>) = MemoryVersionReplacer.replace(state, replacement)

    fun collectFinalVersions(memoryTree: Map<MemoryDescriptor, Map<MemoryVersion, Set<MemoryVersion>>>) = memoryTree.mapValues { findFinalVersion(it.value) }
    fun collectInitialVersions(memoryTree: Map<MemoryDescriptor, Map<MemoryVersion, Set<MemoryVersion>>>) = memoryTree.mapValues { findInitialVersion(it.value) }

    private fun findFinalVersion(memory: Map<MemoryVersion, Set<MemoryVersion>>): MemoryVersion {
        if (memory.isEmpty()) return MemoryVersion.initial()
        val nonFinalVersions = memory.keys
        val finalCandidates = memory.values.flatMap { it - nonFinalVersions }.distinct()
        when (finalCandidates.size) {
            1 -> return finalCandidates.first()
            0 -> error("No final version found")
            else -> error("Too many final candidates")
        }
    }

    private fun findInitialVersion(memory: Map<MemoryVersion, Set<MemoryVersion>>): MemoryVersion {
        val initial = MemoryVersion.initial()
        if (memory.isEmpty()) return initial
        if (initial in memory) return initial
        error("No initial version in memory")
    }

    fun memoryVersionInfo(state: PredicateState) = MemoryVersionInfoCollector.collect(state)

}

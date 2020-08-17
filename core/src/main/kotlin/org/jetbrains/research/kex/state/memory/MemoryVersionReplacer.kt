package org.jetbrains.research.kex.state.memory

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.state.PredicateState

internal class MemoryVersionReplacer(
        val sourceState: PredicateState,
        val replaceFrom: MemoryVersion,
        val replacementState: PredicateState
) {
    init {
        check(replaceFrom.type == MemoryVersionType.NEW) { "Only new supported for replacement" }
    }

    fun replace(): Pair<PredicateState, PredicateState> {
        val replacementVersioner = MemoryVersioner()
        val (replaceState, replaceToInitial, replaceToFinal) = replacementVersioner.setupVersions(replacementState)
        val memoryAccessors = MemoryUtils.collectMemoryAccesses(sourceState)
        val memoryDependency = MemoryUtils.memoryVersionDescendantTree(memoryAccessors).toMutableMap()
        memoryDependency[replacementVersioner.callDescriptor] = MemoryUtils.collectCallMemory(sourceState)
        val descriptorsToInsert = memoryDependency.keys intersect replaceToInitial.keys intersect replaceToFinal.keys
        val sourceMap = hashMapOf<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>()
        val replacementMap = hashMapOf<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>()
        for (descriptor in descriptorsToInsert) {
            val initial = replaceToInitial.getValue(descriptor)
            val final = replaceToFinal.getValue(descriptor)
            val dependencyTree = MemoryUtils.memoryVersionDescendantTree(final)
            val newRoot = replaceFrom.predecessors.first()
            val replacementStartIndex = MemoryUtils.allVersionsUpToRoot(newRoot).filter { it.type != MemoryVersionType.MERGE }.map { it.version }.maxOrNull() ?: 1
            val replacementMapping = createMappingStartingFromRoot(initial, replacementStartIndex, hashMapOf(initial to newRoot)) {
                dependencyTree[it]?.toList() ?: emptyList()
            }
            replacementMap[descriptor] = replacementMapping
            val mappedFinal = replacementMapping[final] ?: error("No final version in mapping")
            val sourceStartIndex = MemoryUtils.allVersionsUpToRoot(mappedFinal).filter { it.type != MemoryVersionType.MERGE }.map { it.version }.maxOrNull() ?: 1
            sourceMap[descriptor] = createMappingStartingFromRoot(replaceFrom, sourceStartIndex, hashMapOf(replaceFrom to mappedFinal)) {
                memoryDependency.getValue(descriptor)[it]?.toList() ?: emptyList()
            }
        }
        val resultSource = OptionalMemoryVersionMapper(sourceMap, replacementVersioner.callDescriptor).apply(sourceState)
        val resultReplacement = OptionalMemoryVersionMapper(replacementMap, replacementVersioner.callDescriptor).apply(replaceState)
        return resultSource to resultReplacement
    }

    private fun createMappingStartingFromRoot(
            root: MemoryVersion,
            startIndex: Int,
            mapping: MutableMap<MemoryVersion, MemoryVersion>,
            children: (MemoryVersion) -> List<MemoryVersion>
    ): Map<MemoryVersion, MemoryVersion> {
        var memoryVersionIdx = startIndex
        val queue = dequeOf(root)
        loop@ while (queue.isNotEmpty()) {
            val node = queue.removeFirst()
            queue += children(node)
            if (node in mapping) continue
            when (node.type) {
                MemoryVersionType.INITIAL -> error("Initial memory is not supported here")
                MemoryVersionType.NEW -> {
                    val parentVersion = mapping[node.predecessors.first()] ?: error("Parent version is not computed")
                    mapping.getOrPut(node) { parentVersion.resetToVersion(memoryVersionIdx++) }
                }
                MemoryVersionType.NORMAL -> {
                    val parentVersion = mapping[node.predecessors.first()] ?: error("Parent version is not computed")
                    mapping.getOrPut(node) { parentVersion.increaseSubversion() }
                }
                MemoryVersionType.MERGE -> {
                    val parentVersionsRaw = node.predecessors.map { mapping[it] }
                    val parentVersions = parentVersionsRaw.filterNotNull()
                    if (parentVersions != parentVersionsRaw) {
                        queue.addLast(node)
                        continue@loop
                    }
                    mapping.getOrPut(node) { MemoryVersion.merge(parentVersions) }
                }
                MemoryVersionType.DEFAULT -> error("Default memory")
            }
        }
        return mapping
    }

}
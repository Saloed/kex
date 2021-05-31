package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kthelper.collection.dequeOf
import org.jetbrains.research.kex.state.PredicateState

object MemoryVersionReplacer {

    fun replace(state: PredicateState, fromVersion: MemoryVersion, toVersion: MemoryVersion): PredicateState {
        val access = MemoryUtils.collectMemoryAccesses(state)
        val tree = MemoryUtils.memoryVersionDescendantTree(access)
        val mapping = tree.mapValues { (_, versionTree) -> replace(versionTree, fromVersion, toVersion) }
        return OptionalMemoryVersionMapper(mapping).apply(state)
    }

    fun replace(state: PredicateState, replacement: Map<MemoryDescriptor, Pair<MemoryVersion, MemoryVersion>>): PredicateState {
        val access = MemoryUtils.collectMemoryAccesses(state)
        val tree = MemoryUtils.memoryVersionDescendantTree(access)
        val mapping = tree.filterKeys { it in replacement }.mapValues { (descriptor, versionTree) ->
            val (from, to) = replacement[descriptor] ?: error("checked in filter")
            replace(versionTree, from, to)
        }
        return OptionalMemoryVersionMapper(mapping).apply(state)
    }

    fun replaceMany(state: PredicateState, replacement: Map<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>): PredicateState {
        val versionInfo = MemoryUtils.memoryVersionInfo(state)
        var result = state
        for ((descriptor, replacements) in replacement) {
            val versionTree = versionInfo.memoryTree[descriptor] ?: error("Descriptor is unknown: $descriptor")
            val orderedReplacements = replacements.entries.sortedWith { left, right -> MemoryVersionComparator.compare(left.key, right.key) }
            TODO()
        }
        return result
    }

    private fun replace(tree: Map<MemoryVersion, Set<MemoryVersion>>, fromVersion: MemoryVersion, toVersion: MemoryVersion): Map<MemoryVersion, MemoryVersion> {
        val mapping = hashMapOf(fromVersion to toVersion)
        val queue = dequeOf(tree[fromVersion] ?: emptySet())
        while (queue.isNotEmpty()) {
            val version = queue.removeFirst()
            if (version in mapping) continue
            val newVersion = when (version.type) {
                MemoryVersionType.INITIAL -> MemoryVersion.initial()
                MemoryVersionType.NEW -> {
                    check(version.predecessors.size == 1) { "New must have a single predecessor" }
                    val parent = version.predecessors.first()
                    val newParent = mapping[parent]
                    when {
                        newParent != null -> newParent.resetToVersion(version.version)
                        parent.dependsOn(fromVersion) -> {
                            queue.addLast(parent)
                            queue.addLast(version)
                            continue
                        }
                        else -> parent.resetToVersion(version.version)
                    }
                }
                MemoryVersionType.NORMAL -> {
                    check(version.predecessors.size == 1) { "New must have a single predecessor" }
                    val parent = version.predecessors.first()
                    val newParent = mapping[parent]
                    when {
                        newParent != null -> newParent.increaseSubversion()
                        parent.dependsOn(fromVersion) -> {
                            queue.addLast(parent)
                            queue.addLast(version)
                            continue
                        }
                        else -> parent.increaseSubversion()
                    }
                }
                MemoryVersionType.MERGE -> {
                    val waitQueue = dequeOf<MemoryVersion>()
                    val newPredecessors = version.predecessors.associateWith { mapping[it] }.mapValues { (original, new) ->
                        when {
                            new != null -> new
                            original.dependsOn(fromVersion) -> {
                                waitQueue.addLast(original)
                                original
                            }
                            else -> original
                        }
                    }
                    if (waitQueue.isNotEmpty()) {
                        queue += waitQueue
                        queue.addLast(version)
                        continue
                    }
                    MemoryVersion.merge(newPredecessors.values.toSet())
                }
                MemoryVersionType.DEFAULT -> MemoryVersion.default()
            }
            mapping[version] = newVersion
            queue += tree[version] ?: emptySet()
        }
        return mapping
    }

}
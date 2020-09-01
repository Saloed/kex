package org.jetbrains.research.kex.state.memory

import com.abdullin.kthelper.collection.dequeOf
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.CallTerm

@Serializable
data class MemoryVersionInfo(val initial: Map<MemoryDescriptor, MemoryVersion>, val final: Map<MemoryDescriptor, MemoryVersion>) {
    val memoryTree by lazy { final.mapValues { MemoryUtils.memoryVersionDescendantTree(it.value) } }
    val allMemoryVersions by lazy { memoryTree.mapValues { (descriptor, _) -> allMemoryVersionForDescriptor(descriptor) } }
    fun findMemoryVersion(descriptor: MemoryDescriptor, version: MemoryVersion) = allMemoryVersions[descriptor]?.get(version)
    private fun allMemoryVersionForDescriptor(descriptor: MemoryDescriptor): Map<MemoryVersion, MemoryVersion> {
        val memories = memoryTree.getValue(descriptor).entries.flatMap { it.value + it.key } + final.getValue(descriptor)
        return memories.associateBy { it }
    }
}

class MemoryVersioner : MemoryVersionTransformer {
    private lateinit var memory: MutableMap<MemoryDescriptor, MemoryVersionSource>
    private lateinit var unsafeMemoryInfo: MemoryVersionInfo
    internal val callDescriptor = MemoryDescriptor(MemoryType.SPECIAL, "__CALL__", 17, MemoryAccessScope.RootScope)

    override fun transformChoice(ps: ChoiceState): PredicateState {
        val currentMemory = memory
        val newChoices = arrayListOf<PredicateState>()
        val memories = arrayListOf(currentMemory)
        for (choice in ps.choices) {
            memory = splitMemory(currentMemory)
            newChoices += transformBase(choice)
            memories += memory
        }
        memory = mergeMemory(memories)
        return ChoiceState(newChoices)
    }

    private fun splitMemory(beforeSplit: Map<MemoryDescriptor, MemoryVersionSource>) = beforeSplit.map { (descriptor, memory) ->
        val newMemory = MemoryVersionSplit(descriptor, memory)
        memory.children += newMemory
        descriptor to newMemory
    }.toMemoryMap()

    private fun mergeMemory(memories: List<Map<MemoryDescriptor, MemoryVersionSource>>) = memories.first().keys.map { descriptor ->
        val memorySources = memories.map { it[descriptor] ?: error("No descriptor $descriptor") }
        val newMemory = MemoryVersionMerge(descriptor, memorySources)
        memorySources.forEach { it.children += newMemory }
        descriptor to newMemory
    }.toMemoryMap()

    private fun newMemory(currentMemory: Map<MemoryDescriptor, MemoryVersionSource>, condition: Any) = currentMemory.map { (descriptor, memory) ->
        val newMemory = MemoryVersionNew(descriptor, memory, condition)
        memory.children += newMemory
        descriptor to newMemory
    }.toMemoryMap()

    override fun transformCall(predicate: CallPredicate): Predicate {
        val call = predicate.call as CallTerm
        val newCall = transform(call) as CallTerm
        memory = newMemory(memory, newCall)
        val newCallVersion = memory.getValue(callDescriptor).version
        val newLhv = predicate.lhvUnsafe?.let { transform(it) }
        return CallPredicate(newLhv, newCall.withMemoryVersion(newCallVersion), predicate.type, predicate.location)
    }

    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val descriptor = element.descriptor()
        val currentMemory = memory[descriptor] ?: error("No memory for descriptor $descriptor")
        if (element.accessType == MemoryAccessType.WRITE) {
            val newMemory = MemoryVersionNormal(descriptor, currentMemory, element)
            currentMemory.children += newMemory
            memory[descriptor] = newMemory
        }
        return element.withMemoryVersion(currentMemory.version)
    }

    fun memoryInfo(): MemoryVersionInfo {
        return unsafeMemoryInfo
    }

    private fun normalizeMemory(memory: Map<MemoryDescriptor, MemoryVersionSource>, versionMappings: Map<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>) = memory
            .mapValues { (descriptor, mvs) ->
                val mapping = versionMappings[descriptor] ?: error("No memory mapping for $descriptor")
                mapping[mvs.version] ?: error("No mapping for version ${mvs.version}")
            }

    override fun apply(ps: PredicateState): PredicateState {
        val accesses = MemoryAccessCollector.collect(ps)
        if (accesses.isEmpty()) {
            unsafeMemoryInfo = MemoryVersionInfo(emptyMap(), emptyMap())
            return ps
        }
        val descriptors = accesses.map { it.descriptor() }.toSet() + callDescriptor
        val initialMemory = descriptors.map { it to MemoryVersionInitial(it) }.toMap()
        memory = initialMemory.toMutableMap()
        val state = super.apply(ps)
        val finalMemory = memory.toMap()
        val versionMappings = memoryVersionNormalizer(initialMemory)
        val result = StrictMemoryVersionMapper(versionMappings, callDescriptor).apply(state)
        val initialMemoryInfo = normalizeMemory(initialMemory, versionMappings).filterKeys { it != callDescriptor }
        val finalMemoryInfo = normalizeMemory(finalMemory, versionMappings).filterKeys { it != callDescriptor }
        unsafeMemoryInfo = MemoryVersionInfo(initialMemoryInfo, finalMemoryInfo)
        MemoryUtils.verify(result, unsafeMemoryInfo)
        return result
    }

    private fun memoryVersionNormalizer(initialMemory: Map<MemoryDescriptor, MemoryVersionSource>) = initialMemory.mapValues { (_, memory) -> memoryVersionNormalizer(memory) }

    private fun memoryVersionNormalizer(root: MemoryVersionSource): Map<MemoryVersion, MemoryVersion> {
        var memoryVersionIdx = 0
        val versionMapping: MutableMap<MemoryVersion, MemoryVersion> = hashMapOf()
        val queue = dequeOf(root)
        while (queue.isNotEmpty()) {
            val node = queue.removeFirst()
            if (node.version in versionMapping) continue
            val newVersion = when (node) {
                is MemoryVersionInitial -> {
                    check(memoryVersionIdx == 0) { "Initial memory is not first" }
                    memoryVersionIdx++
                    MemoryVersion.initial()
                }
                is MemoryVersionNew -> {
                    val parentVersion = versionMapping[node.parent.version]
                    if (parentVersion == null) {
                        queue += node.parent
                        queue += node
                        continue
                    }
                    parentVersion.resetToVersion(memoryVersionIdx++)
                }
                is MemoryVersionNormal -> {
                    val parentVersion = versionMapping[node.parent.version]
                    if (parentVersion == null) {
                        queue += node.parent
                        queue += node
                        continue
                    }
                    parentVersion.increaseSubversion()
                }
                is MemoryVersionMerge -> {
                    val waitQueue = dequeOf<MemoryVersionSource>()
                    val parentVersions = node.memories.mapNotNull {
                        val predecessor = versionMapping[it.version]
                        if (predecessor == null) waitQueue += it
                        predecessor
                    }
                    if (waitQueue.isNotEmpty()) {
                        queue += waitQueue
                        queue += node
                        continue
                    }
                    MemoryVersion.merge(parentVersions)
                }
                is MemoryVersionSplit -> continue
            }
            versionMapping[node.version] = newVersion
            queue += node.children
        }
        return versionMapping
    }
}


private fun List<Pair<MemoryDescriptor, MemoryVersionSource>>.toMemoryMap() = toMap(mutableMapOf())

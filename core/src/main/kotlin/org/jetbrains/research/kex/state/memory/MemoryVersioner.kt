package org.jetbrains.research.kex.state.memory


import com.abdullin.kthelper.algorithm.GraphView
import com.abdullin.kthelper.algorithm.Viewable
import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.CallTerm


class MemoryVersioner : MemoryVersionTransformer {
    private lateinit var memory: MutableMap<MemoryDescriptor, MemoryVersionSource>
    internal val callDescriptor = MemoryDescriptor(MemoryType.SPECIAL, "__CALL__", 17)

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

    fun setupVersions(ps: PredicateState): Triple<PredicateState, Map<MemoryDescriptor, MemoryVersion>, Map<MemoryDescriptor, MemoryVersion>> {
        val accesses = MemoryAccessCollector.collect(ps)
        if (accesses.isEmpty()) return Triple(ps, emptyMap(), emptyMap())
        val descriptors = accesses.map { it.descriptor() }.toSet() + callDescriptor
        val initialMemory = descriptors.map { it to MemoryVersionInitial(it) }.toMap()
        memory = initialMemory.toMutableMap()
        val state = super.apply(ps)
        val finalMemory = memory.toMap()
        val versionMappings = memoryVersionNormalizer(initialMemory)
        val result = StrictMemoryVersionMapper(versionMappings, callDescriptor).apply(state)
        VersionVerifier.apply(result)
        return Triple(result, normalizeMemory(initialMemory, versionMappings), normalizeMemory(finalMemory, versionMappings))
    }

    private fun normalizeMemory(memory: Map<MemoryDescriptor, MemoryVersionSource>, versionMappings: Map<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>) = memory
            .mapValues { (descriptor, mvs) ->
                val mapping = versionMappings[descriptor] ?: error("No memory mapping for $descriptor")
                mapping[mvs.version] ?: error("No mapping for version ${mvs.version}")
            }

    override fun apply(ps: PredicateState): PredicateState {
        val (result, _, _) = setupVersions(ps)
        return result
    }

    private fun memoryVersionNormalizer(initialMemory: Map<MemoryDescriptor, MemoryVersionSource>) = initialMemory.mapValues { (_, memory) -> memoryVersionNormalizer(memory) }

    private fun memoryVersionNormalizer(root: MemoryVersionSource): Map<MemoryVersion, MemoryVersion> {
        var memoryVersionIdx = 0
        val versionMapping: MutableMap<MemoryVersion, MemoryVersion> = hashMapOf()
        val queue = dequeOf(root)
        loop@ while (queue.isNotEmpty()) {
            val node = queue.removeFirst()
            when (node) {
                is MemoryVersionInitial -> {
                    check(memoryVersionIdx == 0) { "Initial memory is not first" }
                    versionMapping.getOrPut(node.version) {
                        memoryVersionIdx++
                        MemoryVersion.initial()
                    }
                }
                is MemoryVersionNew -> {
                    val parentVersion = versionMapping[node.parent.version] ?: error("Parent version is not computed")
                    versionMapping.getOrPut(node.version) { parentVersion.resetToVersion(memoryVersionIdx++) }
                }
                is MemoryVersionNormal -> {
                    val parentVersion = versionMapping[node.parent.version] ?: error("Parent version is not computed")
                    versionMapping.getOrPut(node.version) { parentVersion.increaseSubversion() }
                }
                is MemoryVersionMerge -> {
                    val parentVersionsRaw = node.memories.map { versionMapping[it.version] }
                    val parentVersions = parentVersionsRaw.filterNotNull()
                    if (parentVersions != parentVersionsRaw) {
                        queue.addLast(node)
                        continue@loop
                    }
                    versionMapping.getOrPut(node.version) { MemoryVersion.merge(parentVersions) }
                }
                is MemoryVersionSplit -> {
                }
            }
            queue += node.children
        }
        return versionMapping
    }
}


internal sealed class MemoryVersionSource : Viewable {
    abstract val version: MemoryVersion
    abstract val descriptor: MemoryDescriptor
    val children = arrayListOf<MemoryVersionSource>()
    abstract val graphNode: GraphView
    override val graphView: List<GraphView>
        get() {
            val node = graphNode
            children.forEach { node.addSuccessor(it.graphNode) }
            return listOf(node) + children.flatMap { it.graphView }
        }

    fun view() = view("MemoryVersions", dot, viewer)

    private val dot by lazy {
        kexConfig.getStringValue("view", "dot") ?: unreachable { log.error("Could not find dot") }
    }
    private val viewer by lazy {
        kexConfig.getStringValue("view", "viewer") ?: unreachable { log.error("Could not find viewer") }
    }

}

internal data class MemoryVersionInitial(override val descriptor: MemoryDescriptor) : MemoryVersionSource() {
    override val version: MemoryVersion = MemoryVersion(0, 0, MemoryVersionType.INITIAL, emptySet())
    override val graphNode: GraphView
        get() = GraphView("initial", "initial")
}

internal data class MemoryVersionNew(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource, val condition: Any) : MemoryVersionSource() {
    override val version: MemoryVersion = MemoryVersion(parent.hashCode() * 17 + condition.hashCode(), 0, MemoryVersionType.NEW, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "New $version: $condition")
}

internal data class MemoryVersionNormal(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource, val condition: Any) : MemoryVersionSource() {
    override val version: MemoryVersion = MemoryVersion(parent.hashCode() * 17 + condition.hashCode(), 0, MemoryVersionType.NORMAL, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "Normal $version: $condition")
}

internal data class MemoryVersionMerge(override val descriptor: MemoryDescriptor, val memories: List<MemoryVersionSource>) : MemoryVersionSource() {
    override val version: MemoryVersion = MemoryVersion(memories.hashCode(), 0, MemoryVersionType.MERGE, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "Merge $version")
}

internal data class MemoryVersionSplit(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource) : MemoryVersionSource() {
    override val version: MemoryVersion = parent.version
    override val graphNode: GraphView
        get() = GraphView("split_${parent.graphNode.name}", "Split $version")
}

private fun List<Pair<MemoryDescriptor, MemoryVersionSource>>.toMemoryMap() = toMap(mutableMapOf())



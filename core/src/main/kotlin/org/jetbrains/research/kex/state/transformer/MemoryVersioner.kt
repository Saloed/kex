package org.jetbrains.research.kex.state.transformer

import com.abdullin.kthelper.algorithm.GraphView
import com.abdullin.kthelper.algorithm.Viewable
import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.*
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term


private val dot by lazy { kexConfig.getStringValue("view", "dot") ?: unreachable { log.error("Could not find dot") } }
private val viewer by lazy {
    kexConfig.getStringValue("view", "viewer") ?: unreachable { log.error("Could not find viewer") }
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
}

internal data class MemoryVersionInitial(override val descriptor: MemoryDescriptor) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(0, 0, MemoryVersionType.INITIAL, emptySet())
    override val graphNode: GraphView
        get() = GraphView("initial", "initial")
}

internal data class MemoryVersionNew(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource, val condition: Any) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(parent.hashCode() * 17 + condition.hashCode(), 0, MemoryVersionType.NEW, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "New $version: $condition")
}

internal data class MemoryVersionNormal(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource, val condition: Any) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(parent.hashCode() * 17 + condition.hashCode(), 0, MemoryVersionType.NORMAL, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "Normal $version: $condition")
}

internal data class MemoryVersionMerge(override val descriptor: MemoryDescriptor, val memories: List<MemoryVersionSource>) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(memories.hashCode(), 0, MemoryVersionType.MERGE, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "Merge $version")
}

internal data class MemoryVersionSplit(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = parent.version
    override val graphNode: GraphView
        get() = GraphView("split_${parent.graphNode.name}", "Split $version")
}

private fun List<Pair<MemoryDescriptor, MemoryVersionSource>>.toMemoryMap() = toMap(mutableMapOf())

class MemoryVersioner : MemoryVersionTransformer {
    private lateinit var memory: MutableMap<MemoryDescriptor, MemoryVersionSource>

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
        val newLhv = predicate.lhvUnsafe?.let { transform(it) }
        return CallPredicate(newLhv, newCall, predicate.type, predicate.location)
    }

    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val descriptor = element.descriptor()
        val currentMemory = memory[descriptor] ?: error("No memory for descriptor $descriptor")
        if (element.accessType == MemoryAccessType.WRITE) {
            memory[descriptor] = MemoryVersionNormal(descriptor, currentMemory, element)
        }
        return element.withMemoryVersion(currentMemory.version)
    }

    override fun apply(ps: PredicateState): PredicateState {
        val accesses = MemoryAccessCollector.collect(ps)
        val descriptors = accesses.map { it.descriptor() }.toSet()
        val initialMemory = descriptors.map { it to MemoryVersionInitial(it) }.toMemoryMap()
        memory = initialMemory
        val state = super.apply(ps)
        val finalMemory = memory
        val versionMappings = memoryVersionNormalizer(initialMemory)
        val result = MemoryVersionMapper(versionMappings).apply(state)
        VersionVerifier.apply(result)
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

interface MemoryVersionTransformer : Transformer<MemoryVersionTransformer> {
    fun <T> transformMemoryVersion(element: MemoryAccess<T>): T = element.withMemoryVersion(element.memoryVersion)

    @Suppress("UNCHECKED_CAST")
    override fun transformTerm(term: Term): Term = when (term) {
        is MemoryAccess<*> -> transformMemoryVersion(term as MemoryAccess<Term>)
        else -> term
    }

    @Suppress("UNCHECKED_CAST")
    override fun transformPredicate(predicate: Predicate): Predicate = when (predicate) {
        is MemoryAccess<*> -> transformMemoryVersion(predicate as MemoryAccess<Predicate>)
        else -> predicate
    }
}

private class MemoryVersionMapper(val mapping: Map<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>) : MemoryVersionTransformer {
    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val descriptor = element.descriptor()
        val memoryMapping = mapping[descriptor] ?: error("No memory mapping for $descriptor")
        val newVersion = memoryMapping[element.memoryVersion] ?: error("Version must be updated")
        return element.withMemoryVersion(newVersion)
    }
}

class MemoryAccessCollector private constructor() : MemoryVersionTransformer {
    private val memoryAccesses = arrayListOf<MemoryAccess<*>>()
    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        memoryAccesses += element
        return super.transformMemoryVersion(element)
    }

    companion object {
        fun collect(ps: PredicateState) = MemoryAccessCollector().apply { apply(ps) }.memoryAccesses
    }
}

class MemoryVersionViewer private constructor(val memoryAccess: List<MemoryAccess<*>>) : Viewable {
    private val memoryVersions = hashSetOf<MemoryVersion>()

    init {
        memoryAccess.forEach { deepAddMemoryVersion(it.memoryVersion) }
    }

    private fun deepAddMemoryVersion(memoryVersion: MemoryVersion) {
        memoryVersions += memoryVersion
        memoryVersion.predecessors.forEach { deepAddMemoryVersion(it) }
    }

    override val graphView: List<GraphView>
        get() {
            val views = memoryVersions.map { it to it.graphView() }.toMap()
            for ((memory, view) in views) {
                memory.predecessors.forEach { views[it]?.addSuccessor(view) ?: error("No node for memory $it") }
            }
            return views.values.toList()
        }

    private fun MemoryVersion.graphView() = GraphView("${type}__${version}__${subversion}", "$type $version.$subversion")

    companion object {
        fun view(ps: PredicateState) {
            val memoryAccess = MemoryAccessCollector.collect(ps)
            val viewBuilder = MemoryVersionViewer(memoryAccess)
            viewBuilder.view("MemoryVersions", dot, viewer)
        }
    }
}

object VersionVerifier : MemoryVersionTransformer {
    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        if (element.memoryVersion.type == MemoryVersionType.DEFAULT) {
            error("Default memory: $element")
        }
        return super.transformMemoryVersion(element)
    }
}

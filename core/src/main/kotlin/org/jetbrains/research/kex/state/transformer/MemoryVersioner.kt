package org.jetbrains.research.kex.state.transformer

import com.abdullin.kthelper.algorithm.GraphView
import com.abdullin.kthelper.algorithm.Viewable
import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term


private val dot by lazy { kexConfig.getStringValue("view", "dot") ?: unreachable { log.error("Could not find dot") } }
private val viewer by lazy {
    kexConfig.getStringValue("view", "viewer") ?: unreachable { log.error("Could not find viewer") }
}


internal sealed class MemoryVersionSource : Viewable {
    abstract val version: MemoryVersion
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

internal class MemoryVersionInitial : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(0, MemoryVersionType.INITIAL, null)
    override val graphNode: GraphView
        get() = GraphView("initial", "initial")
}

internal data class MemoryVersionNew(val parent: MemoryVersionSource, val term: Term) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(parent.hashCode() * 17 + term.hashCode(), MemoryVersionType.NORMAL, null)
    override val graphNode: GraphView
        get() = GraphView("$version", "New $version: $term")
}

internal data class MemoryVersionMerge(val memories: List<MemoryVersionSource>) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(memories.hashCode(), MemoryVersionType.MERGE, null)
    override val graphNode: GraphView
        get() = GraphView("$version", "Merge $version")
}

internal data class MemoryVersionSplit(val parent: MemoryVersionSource) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = parent.version
    override val graphNode: GraphView
        get() = GraphView("split_${parent.graphNode.name}", "Split $version")
}

class MemoryVersioner : Transformer<MemoryVersioner> {
    private var memory: MemoryVersionSource = MemoryVersionInitial()
    override fun transformChoice(ps: ChoiceState): PredicateState {
        val currentMemory = memory
        val newChoices = arrayListOf<PredicateState>()
        val memories = arrayListOf<MemoryVersionSource>()
        for (choice in ps.choices) {
            val newMemory = MemoryVersionSplit(currentMemory)
            currentMemory.children += newMemory
            memory = newMemory
            newChoices += transformBase(choice)
            memories += memory
        }
        memory = MemoryVersionMerge(memories)
        memories.forEach { it.children += memory }
        return ChoiceState(newChoices)
    }

    override fun transformCall(predicate: CallPredicate): Predicate {
        val call = predicate.call as CallTerm
        val newCall = transform(call) as CallTerm
        val memoryBeforeCall = memory
        val newMemory = MemoryVersionNew(memoryBeforeCall, newCall)
        memoryBeforeCall.children += newMemory
        memory = newMemory
        val newLhv = predicate.lhvUnsafe?.let { transform(it) }
        return CallPredicate(newLhv, newCall, predicate.type, predicate.location)
    }

    override fun transformTerm(term: Term): Term = term.withMemoryVersion(memory.version)

    override fun apply(ps: PredicateState): PredicateState {
        val memoryRoot = memory
        val state = super.apply(ps)
        val versionMappings = memoryVersionNormalizer(memoryRoot)
        return MemoryVersionMapper(versionMappings).apply(state)
    }

    private class MemoryVersionMapper(val mapping: Map<MemoryVersion, MemoryVersion>) : Transformer<MemoryVersionMapper> {
        override fun transformTerm(term: Term): Term = when (val newVersion = mapping[term.memoryVersion]) {
            null -> term
            else -> term.withMemoryVersion(newVersion)
        }
    }

    private fun memoryVersionNormalizer(root: MemoryVersionSource): Map<MemoryVersion, MemoryVersion> {
        var idx = 0
        var memoryMerges = 0
        val versionMapping: MutableMap<MemoryVersion, MemoryVersion> = hashMapOf()
        val manager = MemoryVersionManager(hashMapOf())
        val queue = dequeOf(root)
        loop@ while (queue.isNotEmpty()) {
            val node = queue.removeFirst()
            when (node) {
                is MemoryVersionInitial -> {
                    check(idx == 0) { "Initial memory is not first" }
                    val newVersion = versionMapping.getOrPut(node.version) { MemoryVersion(idx++, MemoryVersionType.INITIAL, manager) }
                    manager.registerMemoryVersion(newVersion, emptySet())
                }
                is MemoryVersionNew -> {
                    val parentVersion = versionMapping[node.parent.version] ?: error("Parent version is not computed")
                    val newVersion = versionMapping.getOrPut(node.version) { MemoryVersion(idx++, MemoryVersionType.NORMAL, manager) }
                    manager.registerMemoryVersion(newVersion, setOf(parentVersion))
                }
                is MemoryVersionMerge -> {
                    val parentVersionsRaw = node.memories.map { versionMapping[it.version] }
                    val parentVersions = parentVersionsRaw.filterNotNull()
                    if (parentVersions != parentVersionsRaw) {
                        queue.addLast(node)
                        continue@loop
                    }
                    val newVersion = versionMapping.getOrPut(node.version) { MemoryVersion(memoryMerges++, MemoryVersionType.MERGE, manager) }
                    manager.registerMemoryVersion(newVersion, parentVersions.toSet())
                }
                is MemoryVersionSplit -> {
                }
            }
            queue += node.children
        }
        return versionMapping
    }
}
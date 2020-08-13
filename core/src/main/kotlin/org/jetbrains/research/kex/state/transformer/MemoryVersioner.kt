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
import org.jetbrains.research.kex.state.term.MemoryDependentTerm
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
        get() = MemoryVersion(0, MemoryVersionType.INITIAL, emptySet())
    override val graphNode: GraphView
        get() = GraphView("initial", "initial")
}

internal data class MemoryVersionNew(val parent: MemoryVersionSource, val condition: Any) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(parent.hashCode() * 17 + condition.hashCode(), MemoryVersionType.NEW, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "New $version: $condition")
}

internal data class MemoryVersionNormal(val parent: MemoryVersionSource, val condition: Any) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(parent.hashCode() * 17 + condition.hashCode(), MemoryVersionType.NORMAL, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "Normal $version: $condition")
}

internal data class MemoryVersionMerge(val memories: List<MemoryVersionSource>) : MemoryVersionSource() {
    override val version: MemoryVersion
        get() = MemoryVersion(memories.hashCode(), MemoryVersionType.MERGE, emptySet())
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
        memory = newMemory(MemoryVersionNew(memory, newCall))
        val newLhv = predicate.lhvUnsafe?.let { transform(it) }
        return CallPredicate(newLhv, newCall, predicate.type, predicate.location)
    }

    override fun transformArrayStorePredicate(predicate: ArrayStorePredicate): Predicate {
        memory = newMemory(MemoryVersionNormal(memory, predicate))
        return super.transformArrayStorePredicate(predicate)
    }

    override fun transformFieldStorePredicate(predicate: FieldStorePredicate): Predicate {
        memory = newMemory(MemoryVersionNormal(memory, predicate))
        return super.transformFieldStorePredicate(predicate)
    }

    override fun transformNewArray(predicate: NewArrayPredicate): Predicate {
        val tdimentions = predicate.dimentions.map { transform(it) }
        memory = newMemory(MemoryVersionNormal(memory, predicate))
        val tlhv = transform(predicate.lhv)
        return NewArrayPredicate(tlhv, tdimentions, predicate.elementType, predicate.instruction, predicate.type, predicate.location)
    }

    override fun transformNew(predicate: NewPredicate): Predicate {
        memory = newMemory(MemoryVersionNormal(memory, predicate))
        return super.transformNew(predicate)
    }

    override fun transformTerm(term: Term): Term = when (term) {
        is MemoryDependentTerm -> term.withMemoryVersion(memory.version)
        else -> term
    }

    override fun apply(ps: PredicateState): PredicateState {
        val memoryRoot = memory
        val state = super.apply(ps)
        val versionMappings = memoryVersionNormalizer(memoryRoot)
        val result = MemoryVersionMapper(versionMappings).apply(state)
        VersionVerifier.apply(result)
        return result
    }

    private fun newMemory(newMem: MemoryVersionSource): MemoryVersionSource {
        memory.children += newMem
        return newMem
    }

    private class MemoryVersionMapper(val mapping: Map<MemoryVersion, MemoryVersion>) : Transformer<MemoryVersionMapper> {
        override fun transformTerm(term: Term): Term = when (term) {
            is MemoryDependentTerm -> {
                val newVersion = mapping[term.memoryVersion] ?: error("Version must be updated")
                term.withMemoryVersion(newVersion)
            }
            else -> term
        }
    }

    private fun memoryVersionNormalizer(root: MemoryVersionSource): Map<MemoryVersion, MemoryVersion> {
        var newIdx = 0
        var normalIdx = 0
        var memoryMerges = 0
        val versionMapping: MutableMap<MemoryVersion, MemoryVersion> = hashMapOf()
        val queue = dequeOf(root)
        loop@ while (queue.isNotEmpty()) {
            val node = queue.removeFirst()
            when (node) {
                is MemoryVersionInitial -> {
                    check(newIdx == 0) { "Initial memory is not first" }
                    versionMapping.getOrPut(node.version) { MemoryVersion(newIdx++, MemoryVersionType.INITIAL, emptySet()) }
                }
                is MemoryVersionNew -> {
                    val parentVersion = versionMapping[node.parent.version] ?: error("Parent version is not computed")
                    versionMapping.getOrPut(node.version) { MemoryVersion(newIdx++, MemoryVersionType.NEW, setOf(parentVersion)) }
                }
                is MemoryVersionNormal -> {
                    val parentVersion = versionMapping[node.parent.version] ?: error("Parent version is not computed")
                    versionMapping.getOrPut(node.version) { MemoryVersion(normalIdx++, MemoryVersionType.NORMAL, setOf(parentVersion)) }
                }
                is MemoryVersionMerge -> {
                    val parentVersionsRaw = node.memories.map { versionMapping[it.version] }
                    val parentVersions = parentVersionsRaw.filterNotNull()
                    if (parentVersions != parentVersionsRaw) {
                        queue.addLast(node)
                        continue@loop
                    }
                    val uniquePredecessors = parentVersions.toSet()
                    when (uniquePredecessors.size) {
                        0 -> error("Empty memory merge")
                        1 -> versionMapping.getOrPut(node.version) { uniquePredecessors.first() }
                        else -> versionMapping.getOrPut(node.version) { MemoryVersion(memoryMerges++, MemoryVersionType.MERGE, uniquePredecessors) }
                    }
                }
                is MemoryVersionSplit -> {
                }
            }
            queue += node.children
        }
        return versionMapping
    }
}

object VersionVerifier : Transformer<VersionVerifier> {
    override fun transformTerm(term: Term): Term {
        if (term is MemoryDependentTerm && term.memoryVersion.type == MemoryVersionType.DEFAULT) {
            error("term with default memory: $term")
        }
        return term
    }
}
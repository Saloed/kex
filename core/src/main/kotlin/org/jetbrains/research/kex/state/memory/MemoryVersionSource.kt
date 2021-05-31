@file:Suppress("EqualsOrHashCode")

package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kthelper.algorithm.GraphView
import org.jetbrains.research.kthelper.algorithm.Viewable
import org.jetbrains.research.kthelper.assert.unreachable
import org.jetbrains.research.kthelper.defaultHashCode
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.config.kexConfig

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
    private val hash = defaultHashCode(descriptor)
    override fun hashCode(): Int = hash
}

internal data class MemoryVersionNew(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource, val condition: Any, val idx: Int) : MemoryVersionSource() {
    override val version: MemoryVersion = MemoryVersion(31 * idx + parent.hashCode() * 17 + condition.hashCode(), 0, MemoryVersionType.NEW, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "New $idx $version: $condition")
    private val hash = defaultHashCode(descriptor, parent, condition, idx)
    override fun hashCode(): Int = hash
}

internal data class MemoryVersionNormal(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource, val condition: Any) : MemoryVersionSource() {
    override val version: MemoryVersion = MemoryVersion(parent.hashCode() * 17 + condition.hashCode(), 0, MemoryVersionType.NORMAL, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "Normal $version: $condition")
    private val hash = defaultHashCode(descriptor, parent, condition)
    override fun hashCode(): Int = hash
}

internal data class MemoryVersionMerge(override val descriptor: MemoryDescriptor, val memories: List<MemoryVersionSource>) : MemoryVersionSource() {
    override val version: MemoryVersion = MemoryVersion(memories.hashCode(), 0, MemoryVersionType.MERGE, emptySet())
    override val graphNode: GraphView
        get() = GraphView("$version", "Merge $version")
    private val hash = defaultHashCode(descriptor, memories)
    override fun hashCode(): Int = hash
}

internal data class MemoryVersionSplit(override val descriptor: MemoryDescriptor, val parent: MemoryVersionSource) : MemoryVersionSource() {
    override val version: MemoryVersion = parent.version
    override val graphNode: GraphView
        get() = GraphView("split_${parent.graphNode.name}", "Split $version")
    private val hash = defaultHashCode(descriptor, parent)
    override fun hashCode(): Int = hash
}

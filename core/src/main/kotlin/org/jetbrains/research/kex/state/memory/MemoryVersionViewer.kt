package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kthelper.algorithm.GraphView
import org.jetbrains.research.kthelper.algorithm.Viewable
import org.jetbrains.research.kthelper.assert.unreachable
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.state.PredicateState


internal class MemoryVersionViewer private constructor(val memoryAccess: List<MemoryAccess<*>>) : Viewable {
    private val memoryVersions = hashMapOf<MemoryDescriptor, MutableSet<MemoryVersion>>()

    init {
        memoryAccess.forEach { deepAdd(memoryVersions.getOrPut(it.descriptor()) { hashSetOf() }, it.memoryVersion) }
    }

    private fun deepAdd(memoryVersions: MutableSet<MemoryVersion>, memoryVersion: MemoryVersion) {
        memoryVersions += memoryVersion
        memoryVersion.predecessors.forEach { deepAdd(memoryVersions, it) }
    }

    fun addCallInfo(callMemoryTree: Map<MemoryVersion, Set<MemoryVersion>>) {
        val data = memoryVersions.getOrPut(
            MemoryDescriptor(
                MemoryType.SPECIAL,
                "__CALL__",
                17,
                MemoryAccessScope.RootScope
            )
        ) { hashSetOf() }
        callMemoryTree.keys.forEach { deepAdd(data, it) }
        callMemoryTree.values.flatten().forEach { deepAdd(data, it) }
    }

    override val graphView: List<GraphView>
        get() {
            val views = memoryVersions.flatMap { (descriptor, versions) -> versions.map { it to descriptor } }
                .map { it to it.graphView() }.toMap()
            for ((memory, view) in views) {
                memory.first.predecessors.forEach {
                    views[it to memory.second]?.addSuccessor(view) ?: error("No node for memory $it")
                }
            }
            return views.values.toList()
        }

    private fun Pair<MemoryVersion, MemoryDescriptor>.graphView() = GraphView(
        "${first.machineName}__${second.machineName}",
        "${first.humanReadableName}${second.humanReadableName}"
    )

    companion object {
        fun view(ps: PredicateState) {
            val memoryAccess = MemoryAccessCollector.collect(ps)
            val viewBuilder = MemoryVersionViewer(memoryAccess)
            viewBuilder.addCallInfo(MemoryUtils.collectCallMemory(ps))
            viewBuilder.view("MemoryVersions", dot, viewer)
        }

        private val dot by lazy {
            kexConfig.getStringValue("view", "dot") ?: unreachable { log.error("Could not find dot") }
        }
        private val viewer by lazy {
            kexConfig.getStringValue("view", "viewer") ?: unreachable { log.error("Could not find viewer") }
        }

    }
}

internal class MemoryVersionInfoViewer private constructor(val memoryVersion: MemoryVersionInfo) : Viewable {
    override val graphView: List<GraphView>
        get() = memoryVersion.final.flatMap { descriptorView(it.key, it.value) }

    private fun descriptorView(descriptor: MemoryDescriptor, finalVersion: MemoryVersion): List<GraphView> {
        val root = GraphView("${descriptor.machineName}__root", descriptor.humanReadableName)
        val result = mutableListOf(root)
        fun visit(version: MemoryVersion, parent: GraphView) {
            val node = GraphView("${descriptor.machineName}__${version.machineName}", version.humanReadableName)
            result.add(node)
            node.addSuccessor(parent)
            version.predecessors.forEach { visit(it, node) }
        }
        visit(finalVersion, root)
        return result
    }


    companion object {
        fun view(versionInfo: MemoryVersionInfo) {
            val viewBuilder = MemoryVersionInfoViewer(versionInfo)
            viewBuilder.view("MemoryVersions", dot, viewer)
        }

        private val dot by lazy {
            kexConfig.getStringValue("view", "dot") ?: unreachable { log.error("Could not find dot") }
        }
        private val viewer by lazy {
            kexConfig.getStringValue("view", "viewer") ?: unreachable { log.error("Could not find viewer") }
        }

    }
}

package org.jetbrains.research.kex.state.memory

import com.abdullin.kthelper.algorithm.GraphView
import com.abdullin.kthelper.algorithm.Viewable
import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.logging.log
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
        val data = memoryVersions.getOrPut(MemoryDescriptor(MemoryType.SPECIAL, "__CALL__", 17, "")) { hashSetOf() }
        callMemoryTree.keys.forEach { deepAdd(data, it) }
        callMemoryTree.values.flatten().forEach { deepAdd(data, it) }
    }

    override val graphView: List<GraphView>
        get() {
            val views = memoryVersions.flatMap { (descriptor, versions) -> versions.map { it to descriptor } }.map { it to it.graphView() }.toMap()
            for ((memory, view) in views) {
                memory.first.predecessors.forEach {
                    views[it to memory.second]?.addSuccessor(view) ?: error("No node for memory $it")
                }
            }
            return views.values.toList()
        }

    private fun Pair<MemoryVersion, MemoryDescriptor>.graphView() = GraphView("${first.machineName}__${second.machineName}", "${first.humanReadableName}${second.humanReadableName}")

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
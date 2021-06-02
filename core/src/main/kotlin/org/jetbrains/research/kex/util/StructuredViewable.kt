package org.jetbrains.research.kex.util

import info.leadinglight.jdot.ClusterGraph
import info.leadinglight.jdot.Edge
import info.leadinglight.jdot.enums.Color
import info.leadinglight.jdot.enums.Shape
import info.leadinglight.jdot.enums.Style
import info.leadinglight.jdot.impl.AbstractGraph
import info.leadinglight.jdot.impl.Attrs
import info.leadinglight.jdot.impl.Util
import org.jetbrains.research.kthelper.algorithm.GraphView
import org.jetbrains.research.kthelper.collection.dequeOf
import java.io.File
import java.nio.file.Files
import java.nio.file.Path
import info.leadinglight.jdot.Graph as JGraph
import info.leadinglight.jdot.Node as JNode

interface StructuredViewable {
    val graphItem: Item

    fun view(name: String, dot: String, viewer: String): String =
        Util.sh(arrayOf(viewer).plus("file://${toFile(name, dot)}"))

    fun toFile(name: String, dot: String): Path {
        JGraph.setDefaultCmd(dot)
        val rootItem: Item.ItemGroup = when (graphItem) {
            is Item.Node -> Item.ItemGroup(name, graphItem)
            is Item.ItemList -> Item.ItemGroup(name, graphItem)
            is Item.ItemGroup -> graphItem as Item.ItemGroup
        }
        val graph = mkGraph(JGraph(name), rootItem)
        buildItemGroup(graph, graph, rootItem, null)
        addEdges(graph, rootItem)
        graph.setBgColor(Color.X11.transparent)
        val file = graph.dot2file("svg")
        val newFile = "${file.removeSuffix("out")}svg"
        val resultingFile = File(newFile).toPath()
        Files.move(File(file).toPath(), resultingFile)
        return resultingFile
    }

    private fun buildItems(graph: AbstractGraph, item: Item, stopOn: Item?) {
        when (item) {
            is Item.Node -> buildItemNode(item, graph, stopOn)
            is Item.ItemGroup -> buildItemGroup(
                graph,
                mkGraph(ClusterGraph(item.id()), item).also { graph.addGraph(it) },
                item,
                stopOn
            )
            is Item.ItemList -> buildSuccessorsIfNotStop(graph, item, stopOn)
        }
    }

    fun buildItemNode(item: Item.Node, graph: AbstractGraph, stopOn: Item?) {
        val node = JNode(item.id())
        if (item.kind != ItemKind.STUB) {
            node.setLabel(item.label).setFontSize(12.0)
        }
        when (item.kind) {
            ItemKind.NODE -> node.setShape(Shape.box)
            ItemKind.OPERATION -> node.setShape(Shape.circle)
            ItemKind.STUB -> node.setLabel("").setShape(Shape.none).setHeight(0.1).setWidth(0.1)
        }
        graph.addNode(node)
        buildSuccessorsIfNotStop(graph, item, stopOn)
    }

    private fun buildSuccessorsIfNotStop(graph: AbstractGraph, item: Item, stopOn: Item?) {
        if (item == stopOn) return
        when (item) {
            is Item.ItemGroup -> {
            }
            is Item.ItemList -> item.items.forEach {
                buildItems(graph, it, stopOn)
            }
            is Item.Node -> item.successors().forEach { buildItems(graph, it, stopOn) }
        }
    }

    private fun buildItemGroup(graph: AbstractGraph, subGraph: AbstractGraph, item: Item.ItemGroup, stopOn: Item?) {
        val newStop = item.terminateItem ?: stopOn
        buildItems(subGraph, item.item, newStop)
        val terminateItem = item.terminateItem ?: return
        when (terminateItem) {
            is Item.ItemGroup -> {
            }
            is Item.ItemList -> buildItems(graph, terminateItem, stopOn)
            is Item.Node -> terminateItem.successors().forEach { buildItems(graph, it, stopOn) }
        }
    }

    private fun <T : AbstractGraph> mkGraph(graph: T, root: Item.ItemGroup): T {
        graph.attrs.set(Attrs.Key.color, Color.X11.blue)
        graph.attrs.set(Attrs.Key.label, root.label)
        return graph
    }

    private fun addEdges(graph: AbstractGraph, root: Item.ItemGroup) {
        val allEdges = resolveEdges(root.edges()).toSet()
        for (edge in allEdges) {
            val graphEdge = Edge(edge.from.id(), edge.to.id())
            graphEdge.setLabel(edge.label)
            graph.addEdge(graphEdge)
        }
    }

    private fun resolveEdges(edges: List<ItemEdge>): List<ItemEdge> {
        val unresolvedEdges = dequeOf(edges)
        val resolvedEdges = mutableListOf<ItemEdge>()
        while (unresolvedEdges.isNotEmpty()) {
            val edge = unresolvedEdges.removeFirst()
            when (val edgeTo = edge.to) {
                is Item.Node -> resolvedEdges += edge
                is Item.ItemGroup -> {
                    unresolvedEdges += ItemEdge(edge.from, edgeTo.item, edge.label)
                }
                is Item.ItemList -> {
                    unresolvedEdges += edgeTo.items.map { ItemEdge(edge.from, it, edge.label) }
                }
            }
        }
        return resolvedEdges
    }

    sealed class Item {
        abstract fun edges(): List<ItemEdge>
        class ItemGroup(val label: String, val item: Item, val terminateItem: Item? = null) : Item() {
            override fun edges(): List<ItemEdge> = item.edges()
        }

        class Node(val label: String, val kind: ItemKind = ItemKind.NODE) : Item() {
            private val edges = mutableListOf<ItemEdge>()
            fun successors() = edges.map { it.to }
            fun addEdge(item: Item) = edges.add(ItemEdge(this, item, ""))
            fun addEdge(item: Item, label: String) = edges.add(ItemEdge(this, item, label))
            override fun edges(): List<ItemEdge> = edges + successors().flatMap { it.edges() }
        }

        class ItemList(val items: List<Item>) : Item() {
            override fun edges(): List<ItemEdge> = items.flatMap { it.edges() }
        }

        fun id() = System.identityHashCode(this).toString()
        override fun hashCode(): Int = System.identityHashCode(this)
        override fun equals(other: Any?): Boolean = other is Item && id() == other.id()

        companion object {
            fun fromGraphView(graphViews: List<GraphView>): Item {
                if (graphViews.isEmpty()) return ItemList(emptyList())
                val nodes = graphViews.associateWith { Node(it.label) }
                val rootNodes = nodes.keys.toMutableSet()
                for (view in graphViews) {
                    for (succ in view.successors) {
                        rootNodes -= succ
                        nodes[view]?.addEdge(nodes[succ] ?: error("No node for successor"))
                    }
                }
                if (rootNodes.isEmpty()) rootNodes += graphViews.first()
                val resultItems = rootNodes.map { nodes[it] ?: error("No item for root") }
                return ItemList(resultItems)
            }
        }
    }

    enum class ItemKind {
        NODE, OPERATION, STUB
    }

    data class ItemEdge(val from: Item, val to: Item, val label: String)
}


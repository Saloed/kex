package org.jetbrains.research.kex.state.memory

import kotlinx.serialization.Serializable

@Serializable
enum class MemoryVersionType {
    INITIAL, NEW, NORMAL, MERGE, DEFAULT
}

@Serializable
class MemoryVersion(val version: Int, val subversion: Int, val type: MemoryVersionType, val predecessors: Set<MemoryVersion>) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is MemoryVersion) return false
        return type == other.type && version == other.version && subversion == other.subversion
    }

    override fun hashCode(): Int = versionIdentifier()

    private fun versionIdentifier(): Int {
        var result = version + 1
        result = 31 * result + subversion + 1
        result = 31 * result + type.hashCode() + 1
        return result
    }

    val machineName: String
        get() = "${type}!${version}!${subversion}"
    val humanReadableName: String
        get() = "[$type][$version.$subversion]"

    override fun toString(): String = humanReadableName

    fun resetToVersion(newVersion: Int) = MemoryVersion(newVersion, 0, MemoryVersionType.NEW, setOf(this))
    fun increaseSubversion() = MemoryVersion(version, subversion + 1, MemoryVersionType.NORMAL, setOf(this))

    companion object {
        fun default() = MemoryVersion(0, 0, MemoryVersionType.DEFAULT, emptySet())
        fun initial() = MemoryVersion(0, 0, MemoryVersionType.INITIAL, emptySet())
        fun merge(memories: Collection<MemoryVersion>): MemoryVersion {
            val uniqueMemories = memories.toSet()
            val memoryIdentifiers = uniqueMemories.map { it.versionIdentifier() }.sorted()
            val mergedVersion = memoryIdentifiers.reduceOrNull { acc, id -> 31 * acc + id } ?: 0
            return MemoryVersion(mergedVersion, 0, MemoryVersionType.MERGE, uniqueMemories)
        }

        val machineNameRegex = Regex("(\\w+)!(\\d+)!(\\d+)")
        fun fromMachineName(machineName: String): MemoryVersion {
            val (type, version, subversion) = machineNameRegex.matchEntire(machineName)?.destructured
                    ?: error("Bad formatted machine name")
            return MemoryVersion(version.toInt(), subversion.toInt(), MemoryVersionType.valueOf(type), emptySet())
        }
    }
}

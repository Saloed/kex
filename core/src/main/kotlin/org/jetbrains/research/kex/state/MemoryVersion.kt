package org.jetbrains.research.kex.state

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable

@Serializable
enum class MemoryVersionType {
    INITIAL, NEW, NORMAL, MERGE, DEFAULT
}

@Serializable
class MemoryVersion(val version: Int, val subversion: Int, val type: MemoryVersionType, val predecessors: Set<MemoryVersion>) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false
        other as MemoryVersion
        return type == other.type && version == other.version && subversion == other.subversion
    }

    override fun hashCode(): Int = defaultHashCode(type, version, subversion)
    override fun toString(): String = "MemoryVersion($type $version.$subversion)"

    fun resetToVersion(newVersion: Int) = MemoryVersion(newVersion, 0, MemoryVersionType.NEW, setOf(this))
    fun increaseSubversion() = MemoryVersion(version, subversion + 1, MemoryVersionType.NORMAL, setOf(this))

    companion object {
        fun default() = MemoryVersion(0, 0, MemoryVersionType.DEFAULT, emptySet())
        fun initial() = MemoryVersion(0, 0, MemoryVersionType.INITIAL, emptySet())
        fun merge(memories: Collection<MemoryVersion>): MemoryVersion {
            val uniqueMemories = memories.toSet()
            return MemoryVersion(uniqueMemories.hashCode(), 0, MemoryVersionType.MERGE, uniqueMemories)
        }
    }
}

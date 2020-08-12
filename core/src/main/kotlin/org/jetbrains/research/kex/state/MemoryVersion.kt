package org.jetbrains.research.kex.state

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable

@Serializable
enum class MemoryVersionType {
    INITIAL, NORMAL, MERGE, DEFAULT
}

@Serializable
class MemoryVersion(val version: Int, val type: MemoryVersionType, private val unsafeMemoryVersionManager: MemoryVersionManager?) {

    val manager: MemoryVersionManager
        get() = when (type) {
            MemoryVersionType.DEFAULT -> error("Getting manager of default memory is error")
            else -> unsafeMemoryVersionManager ?: error("Memory manager is not initialized")
        }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false
        other as MemoryVersion
        if (version != other.version) return false
        if (type != other.type) return false
        return true
    }

    override fun hashCode(): Int = defaultHashCode(version, type)
    override fun toString(): String = "MemoryVersion(version=$version, type=$type)"

    companion object {
        fun default() = MemoryVersion(0, MemoryVersionType.DEFAULT, null)
    }
}

@Serializable
class MemoryVersionManager(private val predecessorTree: MutableMap<MemoryVersion, Set<MemoryVersion>>) {
    fun registerMemoryVersion(memoryVersion: MemoryVersion, predecessors: Set<MemoryVersion>) {
        predecessorTree.getOrPut(memoryVersion) { predecessors }
    }
}

package org.jetbrains.research.kex.state.memory

import com.abdullin.kthelper.defaultHashCode
import org.jetbrains.research.kex.ktype.KexType

enum class MemoryAccessType {
    READ, WRITE
}

enum class MemoryType {
    PROPERTY, ARRAY, SPECIAL
}

data class MemoryDescriptor(val memoryType: MemoryType, val memoryName: String, val memorySpace: Int, val additionalInfo: String) {
    val machineName: String
        get() = "${memorySpace}__${memoryType}__${additionalInfo}__${memoryName}"
    val humanReadableName: String
        get() = "[$memoryType][$memorySpace]($additionalInfo) $memoryName"

    override fun toString(): String = humanReadableName

    companion object {
        private const val memoryTypePattern = "[A-Za-z0-9]+"
        private const val memoryNamePattern = "[A-Za-z0-9_/\$.]+"
        private const val additionalInfoPattern = "[A-Za-z0-9]+"
        val machineNameRegex = Regex("(\\d+)__($memoryTypePattern)__($additionalInfoPattern)?__($memoryNamePattern)")
        fun fromMachineName(machineName: String): MemoryDescriptor {
            val (memorySpace, memoryType, additionalInfo, memoryName) = machineNameRegex.matchEntire(machineName)?.destructured
                    ?: error("Bad formatted machine name")
            return MemoryDescriptor(MemoryType.valueOf(memoryType), memoryName, memorySpace.toInt(), additionalInfo)
        }
    }
}

interface ElementWithMemoryVersion<T> {
    val memoryVersion: MemoryVersion
    fun withMemoryVersion(memoryVersion: MemoryVersion): T
}

interface MemoryAccess<T> : ElementWithMemoryVersion<T> {
    val memoryType: MemoryType
    val memorySpace: Int
    val memoryName: String
    val accessType: MemoryAccessType
    val memoryValueType: KexType
    val additionalInfo: String

    fun descriptor() = MemoryDescriptor(memoryType, memoryName, memorySpace, additionalInfo)
    fun withAdditionalInfo(additionalInfo: String): T

    fun memoryHash() = defaultHashCode(memoryType, memorySpace, memoryName, accessType, memoryVersion, memoryValueType, additionalInfo)
    fun memoryEquals(other: Any?): Boolean = when (other) {
        !is MemoryAccess<*> -> false
        else -> memoryType == other.memoryType
                && memorySpace == other.memorySpace
                && memoryName == other.memoryName
                && accessType == other.accessType
                && memoryVersion == other.memoryVersion
                && memoryValueType == other.memoryValueType
                && additionalInfo == other.additionalInfo
    }
}
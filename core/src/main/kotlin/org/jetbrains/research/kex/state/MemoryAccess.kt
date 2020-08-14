package org.jetbrains.research.kex.state

import com.abdullin.kthelper.defaultHashCode

enum class MemoryAccessType {
    READ, WRITE
}

enum class MemoryType {
    CLASS_PROPERTY, ARRAY, SPECIAL
}

data class MemoryDescriptor(val memoryType: MemoryType, val memoryName: String, val memorySpace: Int)

interface MemoryAccess<T> {
    val memoryType: MemoryType
    val memorySpace: Int
    val memoryName: String
    val memoryVersion: MemoryVersion
    val accessType: MemoryAccessType

    fun withMemoryVersion(memoryVersion: MemoryVersion): T

    fun descriptor() = MemoryDescriptor(memoryType, memoryName, memorySpace)

    fun memoryHash() = defaultHashCode(memoryType, memorySpace, memoryName, accessType, memoryVersion)
    fun memoryEquals(other: Any?): Boolean = when (other) {
        !is MemoryAccess<*> -> false
        else -> memoryType == other.memoryType
                && memorySpace == other.memorySpace
                && memoryName == other.memoryName
                && accessType == other.accessType
                && memoryVersion == other.memoryVersion
    }
}
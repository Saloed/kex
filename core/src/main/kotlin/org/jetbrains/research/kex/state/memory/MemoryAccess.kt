package org.jetbrains.research.kex.state.memory

import com.abdullin.kthelper.defaultHashCode
import org.jetbrains.research.kex.ktype.KexType

enum class MemoryAccessType {
    READ, WRITE
}

enum class MemoryType {
    PROPERTY, ARRAY, SPECIAL
}

data class MemoryDescriptor(val memoryType: MemoryType, val memoryName: String, val memorySpace: Int)

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

    fun descriptor() = MemoryDescriptor(memoryType, memoryName, memorySpace)

    fun memoryHash() = defaultHashCode(memoryType, memorySpace, memoryName, accessType, memoryVersion, memoryValueType)
    fun memoryEquals(other: Any?): Boolean = when (other) {
        !is MemoryAccess<*> -> false
        else -> memoryType == other.memoryType
                && memorySpace == other.memorySpace
                && memoryName == other.memoryName
                && accessType == other.accessType
                && memoryVersion == other.memoryVersion
                && memoryValueType == other.memoryValueType
    }
}
package org.jetbrains.research.kex.state.memory

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.ktype.KexType

enum class MemoryAccessType {
    READ, WRITE
}

enum class MemoryType {
    PROPERTY, ARRAY, SPECIAL
}

@Serializable
data class MemoryDescriptor(val memoryType: MemoryType, val memoryName: String, val memorySpace: Int, val scopeInfo: MemoryAccessScope) {
    val machineName: String
        get() = "${memorySpace}__${memoryType}__${scopeInfo.machineName()}__${memoryName}"
    val humanReadableName: String
        get() = "[$memoryType][$memorySpace](${scopeInfo.machineName()}) $memoryName"

    override fun toString(): String = humanReadableName
    fun withScope(scopeInfo: MemoryAccessScope) = MemoryDescriptor(memoryType, memoryName, memorySpace, scopeInfo)

    companion object {
        private const val memoryTypePattern = "[A-Za-z0-9]+"
        private const val memoryNamePattern = "[A-Za-z0-9_/\$.]+"
        val machineNameRegex = Regex("(\\d+)__($memoryTypePattern)__(${MemoryAccessScope.scopePattern})?__($memoryNamePattern)")
        fun fromMachineName(machineName: String): MemoryDescriptor {
            val (memorySpace, memoryType, scopeInfo, memoryName) = machineNameRegex.matchEntire(machineName)?.destructured
                    ?: error("Bad formatted machine name")
            return MemoryDescriptor(MemoryType.valueOf(memoryType), memoryName, memorySpace.toInt(), MemoryAccessScope.fromMachineName(scopeInfo))
        }
    }
}

interface ElementWithMemoryVersion<T> {
    val memoryVersion: MemoryVersion
    fun withMemoryVersion(memoryVersion: MemoryVersion): T
}

@Serializable
sealed class MemoryAccessScope {
    abstract fun machineName(): String
    fun withScope(scopeName: String) = Scope(scopeName, this)

    @Serializable
    object RootScope : MemoryAccessScope() {
        override fun machineName(): String = ""
        override fun toString(): String = "Root"
    }

    @Serializable
    data class Scope(val scopeName: String, val parent: MemoryAccessScope) : MemoryAccessScope() {
        override fun machineName(): String = "${parent.machineName()}${SCOPE_DELIMITER}${scopeName}"
    }

    companion object {
        const val SCOPE_DELIMITER = "$"
        const val scopePattern = "[A-Za-z0-9!$SCOPE_DELIMITER]+"
        fun fromMachineName(machineName: String) = machineName.split(SCOPE_DELIMITER).drop(1)
                .fold(RootScope as MemoryAccessScope) { parent, scopeName -> parent.withScope(scopeName) }
    }
}

interface MemoryAccess<T> : ElementWithMemoryVersion<T> {
    val memoryType: MemoryType
    val memorySpace: Int
    val memoryName: String
    val accessType: MemoryAccessType
    val memoryValueType: KexType
    val scopeInfo: MemoryAccessScope

    fun descriptor() = MemoryDescriptor(memoryType, memoryName, memorySpace, scopeInfo)
    fun withScopeInfo(scopeInfo: MemoryAccessScope): T
    fun memoryPrint() = memoryVersion.humanReadableName //+ descriptor().humanReadableName

    fun memoryHash() = defaultHashCode(memoryType, memorySpace, memoryName, accessType, memoryVersion, memoryValueType, scopeInfo)
    fun memoryEquals(other: Any?): Boolean = when (other) {
        !is MemoryAccess<*> -> false
        else -> memoryType == other.memoryType
                && memorySpace == other.memorySpace
                && memoryName == other.memoryName
                && accessType == other.accessType
                && memoryVersion == other.memoryVersion
                && memoryValueType == other.memoryValueType
                && scopeInfo == other.scopeInfo
    }
}
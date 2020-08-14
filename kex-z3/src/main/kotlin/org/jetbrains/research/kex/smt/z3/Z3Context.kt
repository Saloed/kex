package org.jetbrains.research.kex.smt.z3

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.NewObjectIdentifier
import java.util.concurrent.atomic.AtomicInteger
import kotlin.reflect.KClass

typealias ExprFactory = Z3ExprFactory
typealias ValueExpr = Z3ValueExpr

data class VersionedMemory(val memory: Memory_, val version: MemoryVersion, val type: KClass<out ValueExpr>) {
    companion object {
        fun merge(name: String, default: VersionedMemory, cases: List<Pair<Bool_, VersionedMemory>>): VersionedMemory {
            check(cases.all { it.second.type == default.type }) { "Try to merge memories with different element types" }
            val mergedVersion = MemoryVersion.merge(listOf(default.version) + cases.map { it.second.version })
            val memories = cases.map { it.first to it.second.memory }
            return VersionedMemory(Memory_.merge(default.memory, memories), mergedVersion, default.type)
        }
    }

    fun <T : ValueExpr> load(ptr: Ptr_, type: KClass<out ValueExpr>) = memory.load<T>(ptr, type)
    fun <T : Dynamic_> store(index: Ptr_, element: T, type: KClass<out ValueExpr>) = VersionedMemory(memory.store(index, element), version.increaseSubversion(), type)
    operator fun get(index: Ptr_) = memory[index]
    operator fun <T : Dynamic_> set(index: Ptr_, element: T, type: KClass<out ValueExpr>) = store(index, element, type)
}

internal data class VersionedMemoryDescriptor(val descriptor: MemoryDescriptor, val primaryVersion: Int)

class Z3Context : Z3SMTContext {
    companion object {
        const val BASE_LOCAL_PTR = (1 shl 10) + 1
        const val BASE_STATIC_PTR = (1 shl 24) + 1
        const val BASE_TYPE_IDX = 100
        const val TYPE_IDX_MULTIPLIER = 10

        fun memoryName(descriptor: MemoryDescriptor, version: MemoryVersion) = "${version.type}_${version.version}_${descriptor.memorySpace}__${descriptor.memoryType}__${descriptor.memoryName}"

        fun create(factory: ExprFactory) = Z3Context(factory, BASE_LOCAL_PTR, BASE_STATIC_PTR)
    }

    val factory: ExprFactory
    private val localPointer: AtomicInteger
    private val localObjPointers: MutableMap<NewObjectIdentifier, Int>
    private val localTypes: MutableMap<Int, KexType>
    private val staticPointer: AtomicInteger
    private val staticObjPointers: MutableMap<NewObjectIdentifier, Int>
    private val staticTypes: MutableMap<Int, KexType>
    private val typeIndex: AtomicInteger
    private val typeMap: MutableMap<KexType, Int>
    private val initialMemories: MutableMap<MemoryDescriptor, VersionedMemory>
    private var activeMemories: MutableMap<MemoryDescriptor, VersionedMemory>
    private var archiveMemories: MutableMap<VersionedMemoryDescriptor, VersionedMemory>

    private constructor(factory: ExprFactory,
                        activeMemories: MutableMap<MemoryDescriptor, VersionedMemory>,
                        initialMemories: MutableMap<MemoryDescriptor, VersionedMemory>,
                        archiveMemories: MutableMap<VersionedMemoryDescriptor, VersionedMemory>,
                        localPointer: AtomicInteger, staticPointer: AtomicInteger,
                        localObjPointers: MutableMap<NewObjectIdentifier, Int>, staticObjPointers: MutableMap<NewObjectIdentifier, Int>,
                        localTypes: MutableMap<Int, KexType>, staticTypes: MutableMap<Int, KexType>,
                        typeIndex: AtomicInteger, typeMap: MutableMap<KexType, Int>) {
        this.factory = factory

        this.activeMemories = activeMemories
        this.initialMemories = initialMemories
        this.archiveMemories = archiveMemories

        this.localPointer = localPointer
        this.localObjPointers = localObjPointers
        this.localTypes = localTypes
        this.staticPointer = staticPointer
        this.staticObjPointers = staticObjPointers
        this.staticTypes = staticTypes

        this.typeIndex = typeIndex
        this.typeMap = typeMap
    }

    constructor(factory: ExprFactory, localPointer: Int, staticPointer: Int)
            : this(factory,
            hashMapOf(), hashMapOf(), hashMapOf(),
            AtomicInteger(localPointer), AtomicInteger(staticPointer),
            hashMapOf(), hashMapOf(), hashMapOf(), hashMapOf(),
            AtomicInteger(BASE_TYPE_IDX), hashMapOf()
    )

    fun emptyMemory(descriptor: MemoryDescriptor, version: MemoryVersion, type: KClass<out ValueExpr>): VersionedMemory {
        val memoryName = memoryName(descriptor, version)
        val memory = factory.makeEmptyMemory(memoryName, type)
        return VersionedMemory(memory, version, type)
    }

    @Deprecated("Access memory without memory access descriptor is deprecated")
    fun getInitialMemory(memoryType: MemoryType, memoryName: String, memorySpace: Int, type: KClass<out ValueExpr>): VersionedMemory {
        val descriptor = MemoryDescriptor(memoryType, memoryName, memorySpace)
        return initialMemories.getOrElse(descriptor) { emptyMemory(descriptor, MemoryVersion.initial(), type) }
    }

    @Deprecated("Access memory without memory access descriptor is deprecated")
    fun getMemory(memoryType: MemoryType, memoryName: String, memorySpace: Int, type: KClass<out ValueExpr>): VersionedMemory {
        val descriptor = MemoryDescriptor(memoryType, memoryName, memorySpace)
        return activeMemories.getOrElse(descriptor) { getInitialMemory(memoryType, memoryName, memorySpace, type) }
    }

    private fun getInitialMemory(descriptor: MemoryDescriptor, version: MemoryVersion, type: KClass<out ValueExpr>) = initialMemories.getOrPut(descriptor) { emptyMemory(descriptor, version, type) }
    private fun getMemoryInternal(memoryAccess: MemoryAccess<*>, type: KClass<out ValueExpr>): VersionedMemory {
        val descriptor = memoryAccess.descriptor()
        val version = memoryAccess.memoryVersion
        check(version.type != MemoryVersionType.DEFAULT) { "Default memory" }
        val versionedDescriptor = VersionedMemoryDescriptor(descriptor, version.version)
        val memory = activeMemories.getOrElse(descriptor) { archiveMemories[versionedDescriptor] }
                ?: error("Memory is not initialized for $descriptor")
        check(memory.version == version) { "Try to get memories with different versions" }
        return memory
    }

    private fun setMemoryInternal(memoryAccess: MemoryAccess<*>, memory: VersionedMemory) {
        val descriptor = memoryAccess.descriptor()
        val version = memoryAccess.memoryVersion
        check(version == memory.version) { "Memory access and memory versions are different" }
        val currentMemory = activeMemories[descriptor] ?: error("No active memory for $descriptor")
        check(currentMemory.version in version.predecessors) { "Incorrect memory write order" }
        activeMemories[descriptor] = memory
    }

    fun getInitialMemory(memoryAccess: MemoryAccess<*>, type: KClass<out ValueExpr>) = initialMemories.getOrElse(memoryAccess.descriptor()) { getMemory(memoryAccess, type) }
    fun getInitialProperties(memoryAccess: MemoryAccess<*>, type: KClass<out ValueExpr>) = initialMemories.getOrElse(memoryAccess.descriptor()) { getProperties(memoryAccess, type) }

    fun getMemory(memoryAccess: MemoryAccess<*>, type: KClass<out ValueExpr>) = getMemoryInternal(memoryAccess, type)
    fun setMemory(memoryAccess: MemoryAccess<*>, memory: VersionedMemory) = setMemoryInternal(memoryAccess, memory)
    fun getProperties(memoryAccess: MemoryAccess<*>, type: KClass<out ValueExpr>) = getMemoryInternal(memoryAccess, type)
    fun setProperties(memoryAccess: MemoryAccess<*>, memory: VersionedMemory) = setMemoryInternal(memoryAccess, memory)

    fun <T : ValueExpr> readMemory(ptr: Ptr_, memoryAccess: MemoryAccess<*>, type: KClass<out ValueExpr>) = getMemory(memoryAccess, type).load<T>(ptr, type)
    fun <T : ValueExpr> writeMemory(ptr: Ptr_, value: T, memoryAccess: MemoryAccess<*>, type: KClass<out ValueExpr>) = setMemory(memoryAccess, getMemory(memoryAccess, type).store(ptr, value, type))

    fun getLocalPtr(identifier: NewObjectIdentifier, size: Int): Ptr_ {
        val ptr = localObjPointers.getOrPut(identifier) { localPointer.getAndAdd(size) }
        localTypes[ptr] = identifier.type
        return factory.makePtrConst(ptr)
    }

    fun getStaticPtr(identifier: NewObjectIdentifier, size: Int): Ptr_ {
        val ptr = staticObjPointers.getOrPut(identifier) { staticPointer.getAndAdd(size) }
        staticTypes[ptr] = identifier.type
        return factory.makePtrConst(ptr)
    }

    fun getTypeIdx(type: KexType) = typeMap.getOrPut(type) { typeIndex.addAndGet(TYPE_IDX_MULTIPLIER) }
    fun getTypeByIdx(idx: Int): KexType? = typeMap.entries.firstOrNull { it.value == idx }?.key
    fun getTypeMapping(): Map<KexType, Int> = typeMap.toMap()

    fun getLocalsTypeMapping() = localTypes.toMap()
    fun getStaticsTypeMapping() = staticTypes.toMap()
    fun getLocals() = localObjPointers.toMap()
    fun getStatics() = staticObjPointers.toMap()
    fun accessRawMemories() = this.activeMemories

    fun splitMemory() = Z3Context(factory, activeMemories.toMutableMap(), initialMemories, archiveMemories, localPointer, staticPointer, localObjPointers, staticObjPointers, localTypes, staticTypes, typeIndex, typeMap)
    fun mergeMemory(name: String, contexts: Map<Bool_, Z3Context>) {
        TODO()
    }


}

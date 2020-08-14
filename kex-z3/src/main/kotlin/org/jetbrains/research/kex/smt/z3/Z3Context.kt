package org.jetbrains.research.kex.smt.z3

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.MemoryVersionType
import org.jetbrains.research.kex.state.predicate.NewObjectIdentifier
import java.util.concurrent.atomic.AtomicInteger
import kotlin.reflect.KClass

typealias ExprFactory = Z3ExprFactory
typealias ValueExpr = Z3ValueExpr

data class MemoryDescriptor(val name: String, val version: Int)

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

class Z3Context : Z3SMTContext {
    companion object {
        const val MEMORY_NAME = "__memory__"
        const val PROPERTY_NAME = "__property__"
        const val TYPE_PROPERTY = "__type__"

        const val BASE_LOCAL_PTR = (1 shl 10) + 1
        const val BASE_STATIC_PTR = (1 shl 24) + 1
        const val BASE_TYPE_IDX = 100
        const val TYPE_IDX_MULTIPLIER = 10

        fun memoryName(memspace: Int) = "${MEMORY_NAME}${memspace}"
        fun propertyName(memspace: Int, name: String) = "${PROPERTY_NAME}${memspace}__${name}"
        fun addMemoryVersion(memoryName: String, version: MemoryVersion) = "${version.type}_${version.version}${memoryName}"

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
    private val initialMemories: MutableMap<String, VersionedMemory>
    private var memories: MutableMap<MemoryDescriptor, VersionedMemory>

    private constructor(factory: ExprFactory, memories: MutableMap<MemoryDescriptor, VersionedMemory>, initialMemories: MutableMap<String, VersionedMemory>,
                        localPointer: AtomicInteger, staticPointer: AtomicInteger,
                        localObjPointers: MutableMap<NewObjectIdentifier, Int>, staticObjPointers: MutableMap<NewObjectIdentifier, Int>,
                        localTypes: MutableMap<Int, KexType>, staticTypes: MutableMap<Int, KexType>,
                        typeIndex: AtomicInteger, typeMap: MutableMap<KexType, Int>) {
        this.factory = factory
        this.memories = memories
        this.initialMemories = initialMemories

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
            : this(factory, hashMapOf(), hashMapOf(), AtomicInteger(localPointer), AtomicInteger(staticPointer), hashMapOf(), hashMapOf(), hashMapOf(), hashMapOf(), AtomicInteger(BASE_TYPE_IDX), hashMapOf())

    fun emptyMemory(name: String, version: MemoryVersion, type: KClass<out ValueExpr>): VersionedMemory {
        val memory = factory.makeEmptyMemory(addMemoryVersion(name, version), type)
        return VersionedMemory(memory, version, type)
    }

    private fun getInitialMemory(name: String, version: MemoryVersion, type: KClass<out ValueExpr>) = initialMemories.getOrPut(name) { emptyMemory(name, version, type) }
    private fun getMemory(name: String, version: MemoryVersion, type: KClass<out ValueExpr>): VersionedMemory {
        val descriptor = MemoryDescriptor(name, version.version)
        return when (version.type) {
            MemoryVersionType.INITIAL -> memories.getOrPut(descriptor) { getInitialMemory(name, version, type) }
            MemoryVersionType.NEW -> memories.getOrPut(descriptor) { emptyMemory(name, version, type) }
            MemoryVersionType.MERGE, MemoryVersionType.NORMAL -> memories[descriptor]
                    ?: error("Memory is not present: $version")
            MemoryVersionType.DEFAULT -> error("Default memory")
        }
    }

    private fun setMemory(name: String, memory: VersionedMemory) {
        val descriptor = MemoryDescriptor(name, memory.version.version)
        memories[descriptor] = memory
    }

    fun getInitialMemory(version: MemoryVersion, memspace: Int, type: KClass<out ValueExpr>) = initialMemories.getOrElse(memoryName(memspace)) { getMemory(version, memspace, type) }
    fun getInitialProperties(name: String, version: MemoryVersion, memspace: Int, type: KClass<out ValueExpr>) = initialMemories.getOrElse(propertyName(memspace, name)) { getProperties(name, version, memspace, type) }

    fun getMemory(version: MemoryVersion, memspace: Int, type: KClass<out ValueExpr>) = getMemory(memoryName(memspace), version, type)
    fun setMemory(memspace: Int, memory: VersionedMemory) = setMemory(memoryName(memspace), memory)
    fun getProperties(propertyName: String, version: MemoryVersion, memspace: Int, type: KClass<out ValueExpr>) = getMemory(propertyName(memspace, propertyName), version, type)
    fun setProperties(propertyName: String, memspace: Int, memory: VersionedMemory) = setMemory(propertyName(memspace, propertyName), memory)

    fun <T : ValueExpr> readMemory(ptr: Ptr_, version: MemoryVersion, memspace: Int, type: KClass<out ValueExpr>) = getMemory(version, memspace, type).load<T>(ptr, type)
    fun <T : ValueExpr> writeMemory(ptr: Ptr_, value: T, version: MemoryVersion, memspace: Int, type: KClass<out ValueExpr>) = setMemory(memspace, getMemory(version, memspace, type).store(ptr, value, type))
    fun <T : ValueExpr> readProperty(ptr: Ptr_, version: MemoryVersion, memspace: Int, name: String, type: KClass<out ValueExpr>) = getProperties(name, version, memspace, type).load<T>(ptr, type)
    fun <T : ValueExpr> writeProperty(ptr: Ptr_, version: MemoryVersion, memspace: Int, name: String, prop: T, type: KClass<out ValueExpr>) = setProperties(name, memspace, getProperties(name, version, memspace, type).store(ptr, prop, type))

    fun getLocalPtr(identifier: NewObjectIdentifier, version: MemoryVersion, size: Int): Ptr_ {
        val ptr = localObjPointers.getOrPut(identifier) { localPointer.getAndAdd(size) }
        localTypes[ptr] = identifier.type
        return factory.makePtrConst(ptr)
    }

    fun getStaticPtr(identifier: NewObjectIdentifier, version: MemoryVersion, size: Int): Ptr_ {
        val ptr = staticObjPointers.getOrPut(identifier) { staticPointer.getAndAdd(size) }
        staticTypes[ptr] = identifier.type
        return factory.makePtrConst(ptr)
    }

    fun getTypeIdx(type: KexType) = typeMap.getOrPut(type) { typeIndex.addAndGet(TYPE_IDX_MULTIPLIER) }
    fun getTypeByIdx(idx: Int): KexType? = typeMap.entries.firstOrNull { it.value == idx }?.key
    fun getTypeMapping(): Map<KexType, Int> = typeMap.toMap()

    fun readType(ptr: Ptr_, version: MemoryVersion, memspace: Int): Int_ = readProperty(ptr, version, memspace, TYPE_PROPERTY, Int_::class)
    fun writeType(ptr: Ptr_, type: Int, version: MemoryVersion, memspace: Int) = writeProperty(ptr, version, memspace, TYPE_PROPERTY, factory.makeIntConst(type), Int_::class)

    fun getLocalsTypeMapping() = localTypes.toMap()
    fun getStaticsTypeMapping() = staticTypes.toMap()
    fun getLocals() = localObjPointers.toMap()
    fun getStatics() = staticObjPointers.toMap()
    fun accessRawMemories() = this.memories

    fun splitMemory() = Z3Context(factory, memories.toMutableMap(), initialMemories, localPointer, staticPointer, localObjPointers, staticObjPointers, localTypes, staticTypes, typeIndex, typeMap)
    fun mergeMemory(name: String, contexts: Map<Bool_, Z3Context>) {
        val defaultMemory = memories.entries.groupBy({ it.key.name }, { it.value })
        val alternativeMemory = contexts.map { (cond, ctx) -> ctx.memories.entries.groupBy({ it.key.name }, { cond to it.value }) }
        check(alternativeMemory.all { it.keys == defaultMemory.keys }) { "Memory is not properly initialized" }
        val mergedMemory = defaultMemory.flatMap { (id, default) ->
            val alternatives = alternativeMemory.flatMap { it[id] ?: error("No memory for id $id") }
            val merged = mergeVersions(name, default, alternatives)
            merged.map { MemoryDescriptor(id, it.version.version) to it }
        }
        memories.plusAssign(mergedMemory)
    }

    private fun mergeVersions(name: String, default: List<VersionedMemory>, alternatives: List<Pair<Bool_, VersionedMemory>>): List<VersionedMemory> {
        check(default.groupBy { it.version.version }.values.all { it.size == 1 }) { "Oops!" }
        val defaults = default.map { it.version.version to it }.toMap()
        val others = alternatives.groupBy { it.second.version.version }
        val updatedDefaults = others.filterKeys { it in defaults.keys }
                .map { (key, value) ->
                    val defaultMemory = defaults[key] ?: error("impossible")
                    val changedMemories = value.filter { it.second != defaultMemory }
                    defaultMemory to changedMemories
                }
                .filter { it.second.isNotEmpty() }
                .map { (defaultMemory, otherMemories) -> VersionedMemory.merge(name, defaultMemory, otherMemories) }


        return updatedDefaults
    }

}

package org.jetbrains.research.kex.smt.z3

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.*
import org.jetbrains.research.kex.state.predicate.NewObjectIdentifier
import java.util.concurrent.atomic.AtomicInteger
import kotlin.reflect.KClass

data class VersionedMemory(val memory: Memory_<Ptr_, Dynamic_>, val version: MemoryVersion, val type: KClass<out Dynamic_>) {
    @Suppress("UNUSED_PARAMETER")
    fun merge(name: String, cases: List<Pair<Bool_, VersionedMemory>>): VersionedMemory {
        check(cases.all { it.second.type == type }) { "Try to merge memories with different element types" }
        val mergedVersion = MemoryVersion.merge(listOf(version) + cases.map { it.second.version })
        val memories = cases.map { it.first to it.second.memory }
        return VersionedMemory(Memory_.merge(memory, memories), mergedVersion, type)
    }

    fun <T : Dynamic_> load(ptr: Ptr_, type: KClass<out Dynamic_>) = memory.load<T>(ptr, type)
    fun <T : Dynamic_> store(index: Ptr_, element: T, type: KClass<out Dynamic_>) = VersionedMemory(memory.store(index, element), version.increaseSubversion(), type)
    operator fun get(index: Ptr_) = memory[index]
    operator fun <T : Dynamic_> set(index: Ptr_, element: T, type: KClass<out Dynamic_>) = store(index, element, type)
}

internal data class VersionedMemoryDescriptor(val descriptor: MemoryDescriptor, val version: MemoryVersion)

class Z3Context : Z3SMTContext {
    companion object {
        const val BASE_LOCAL_PTR = (1 shl 10) + 1
        const val BASE_STATIC_PTR = (1 shl 24) + 1
        const val BASE_TYPE_IDX = 100
        const val TYPE_IDX_MULTIPLIER = 10

        fun memoryName(descriptor: MemoryDescriptor, version: MemoryVersion) = "${version.machineName}__${descriptor.machineName}"

        fun create(factory: ExprFactory_) = Context_(factory, BASE_LOCAL_PTR, BASE_STATIC_PTR)
        fun createInitialized(factory: ExprFactory_, vararg states: PredicateState): Context_ {
            val memoryAccess = states.flatMap { MemoryUtils.collectMemoryAccesses(it) }
            return create(factory).apply { initialize(memoryAccess) }
        }
    }

    val factory: ExprFactory_
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

    private constructor(factory: ExprFactory_,
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

    constructor(factory: ExprFactory_, localPointer: Int, staticPointer: Int)
            : this(factory,
            hashMapOf(), hashMapOf(), hashMapOf(),
            AtomicInteger(localPointer), AtomicInteger(staticPointer),
            hashMapOf(), hashMapOf(), hashMapOf(), hashMapOf(),
            AtomicInteger(BASE_TYPE_IDX), hashMapOf()
    )

    @Deprecated("Access memory without memory access descriptor is deprecated")
    fun getInitialMemory(memoryType: MemoryType, memoryName: String, memorySpace: Int, type: KexType): VersionedMemory {
        val descriptor = MemoryDescriptor(memoryType, memoryName, memorySpace, MemoryAccessScope.RootScope)
        return initialMemories.getOrElse(descriptor) { emptyMemory(descriptor, MemoryVersion.initial(), ExprFactory_.getType(type)) }
    }

    @Deprecated("Access memory without memory access descriptor is deprecated")
    fun getMemory(memoryType: MemoryType, memoryName: String, memorySpace: Int, type: KexType): VersionedMemory {
        val descriptor = MemoryDescriptor(memoryType, memoryName, memorySpace, MemoryAccessScope.RootScope)
        return activeMemories.getOrElse(descriptor) { getInitialMemory(memoryType, memoryName, memorySpace, type) }
    }

    @Deprecated("Access memory without memory access descriptor is deprecated")
    fun <T : Dynamic_> readMemory(ptr: Ptr_, memoryDescriptor: MemoryDescriptor, memoryVersion: MemoryVersion, type: KexType) = getMemory(memoryDescriptor, memoryVersion).load<T>(ptr, ExprFactory_.getType(type))

    @Deprecated("Access memory without memory access descriptor is deprecated")
    fun <T : Dynamic_> writeMemory(ptr: Ptr_, value: T, memoryDescriptor: MemoryDescriptor, memoryVersion: MemoryVersion, type: KexType) = setMemory(memoryDescriptor, memoryVersion, getMemory(memoryDescriptor, memoryVersion).store(ptr, value, ExprFactory_.getType(type)))

    fun initialize(memoryAccess: List<MemoryAccess<*>>) = memoryAccess
            .groupBy { it.descriptor() }
            .mapValues { (_, v) -> v.first() }
            .forEach { (_, memoryAccess) ->
                val memoryType = ExprFactory_.getType(memoryAccess.memoryValueType)
                initialMemories[memoryAccess.descriptor()] = emptyMemory(memoryAccess.descriptor(), MemoryVersion.initial(), memoryType)
            }

    fun resetMemory() {
        activeMemories = initialMemories.toMutableMap()
        archiveMemories.clear()
    }

    fun <T : Dynamic_> readMemory(ptr: Ptr_, memoryAccess: MemoryAccess<*>, type: KClass<out Dynamic_>) = getMemory(memoryAccess).load<T>(ptr, type)
    fun <T : Dynamic_> writeMemory(ptr: Ptr_, value: T, memoryAccess: MemoryAccess<*>, type: KClass<out Dynamic_>) = setMemory(memoryAccess, getMemory(memoryAccess).store(ptr, value, type))

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

    fun splitMemory() = Context_(factory,
            activeMemories.toMutableMap(), initialMemories, archiveMemories.toMutableMap(),
            localPointer, staticPointer, localObjPointers, staticObjPointers,
            localTypes, staticTypes, typeIndex, typeMap)

    fun resetMemoryToVersion(version: MemoryVersion) = activeMemories
            .mapValues { (descriptor, memory) -> emptyMemory(descriptor, version, memory.type) }
            .forEach { (descriptor, newMemory) -> setMemory(descriptor, version, newMemory) }

    fun mergeMemory(name: String, contexts: Map<Bool_, Context_>) {
        check(contexts.values.all { it.activeMemories.keys == activeMemories.keys }) { "Inconsistent memory keys in merge" }
        activeMemories = activeMemories.mapValues { (descriptor, defaultMemory) ->
            val alternatives = contexts.map { (condition, ctx) ->
                val memory = ctx.activeMemories.getValue(descriptor)
                ctx.updateArchive(descriptor, memory)
                condition to memory
            }
            updateArchive(descriptor, defaultMemory)
            defaultMemory.merge(name, alternatives)
        }.toMutableMap()
        mergeArchiveMemories(contexts)
    }

    private fun emptyMemory(descriptor: MemoryDescriptor, version: MemoryVersion, type: KClass<out Dynamic_>): VersionedMemory {
        val memoryName = memoryName(descriptor, version)
        val memory = factory.makeEmptyMemory(memoryName, type)
        return VersionedMemory(memory, version, type)
    }

    private fun getMemory(memoryAccess: MemoryAccess<*>) = getMemory(memoryAccess.descriptor(), memoryAccess.memoryVersion)
    private fun setMemory(memoryAccess: MemoryAccess<*>, memory: VersionedMemory) = setMemory(memoryAccess.descriptor(), memory.version, memory)

    private fun getMemory(descriptor: MemoryDescriptor, version: MemoryVersion): VersionedMemory {
        check(version.type != MemoryVersionType.DEFAULT) { "Default memory" }
        val activeMemory = activeMemories[descriptor]
        if (activeMemory != null && activeMemory.version == version) return activeMemory
        val versionedDescriptor = VersionedMemoryDescriptor(descriptor, version)
        val archiveMemory = archiveMemories[versionedDescriptor] ?: error("Memory is not initialized for $descriptor")
        check(archiveMemory.version == version) { "Try to get memories with different versions" }
        return archiveMemory
    }

    private fun setMemory(descriptor: MemoryDescriptor, version: MemoryVersion, memory: VersionedMemory) {
        check(version == memory.version) { "Memory access and memory versions are different" }
        val currentMemory = activeMemories[descriptor] ?: error("No active memory for $descriptor")
        check(currentMemory.version in version.predecessors) { "Incorrect memory write order" }
        updateArchive(descriptor, currentMemory)
        activeMemories[descriptor] = memory
    }

    private fun updateArchive(descriptor: MemoryDescriptor, memory: VersionedMemory) {
        val versionedDescriptor = VersionedMemoryDescriptor(descriptor, memory.version)
        val oldArchiveRecord = archiveMemories.put(versionedDescriptor, memory) ?: return
        check(oldArchiveRecord == memory) { "Incorrect archive memory write" }
    }

    private fun mergeArchiveMemories(contexts: Map<Bool_, Context_>) {
        val enumeratedContexts = contexts.entries.toList()
        val otherArchives = enumeratedContexts.mapIndexed { index, entry -> entry.value.archiveMemories to index }
        archiveMemories = (otherArchives + (archiveMemories to -1))
                .flatMap { (archive, ctxId) -> archive.entries.map { it to ctxId } }
                .groupBy({ it.first.key }, { it.first.value to it.second })
                .mapValues { (descriptor, records) -> mergeArchiveRecords(descriptor, records, enumeratedContexts) }
                .toMutableMap()
    }

    private fun mergeArchiveRecords(descriptor: VersionedMemoryDescriptor, records: List<Pair<VersionedMemory, Int>>, enumeratedContexts: List<Map.Entry<Bool_, Context_>>): VersionedMemory {
        val memoryPrototype = records.first().first
        if (records.all { it.first == memoryPrototype }) return memoryPrototype
        val conditionedRecords = records.filterNot { it.second == -1 }.map { enumeratedContexts[it.second].key to it.first }
        val defaultRecord = records.find { it.second == -1 }?.first ?: archiveMergeError(descriptor, memoryPrototype)
        return defaultRecord.merge("archive_merge", conditionedRecords)
    }

    private fun archiveMergeError(descriptor: VersionedMemoryDescriptor, memoryPrototype: VersionedMemory): VersionedMemory {
        val memoryName = memoryName(descriptor.descriptor, descriptor.version)
        val errorMemoryName = "archive_merge_error_\$_$memoryName"
        val memory = factory.makeEmptyMemory(errorMemoryName, memoryPrototype.type)
        return VersionedMemory(memory, descriptor.version, memoryPrototype.type)
    }
}

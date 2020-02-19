package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.Context

abstract class Z3MemoryProxy<in Index : Z3BV> : Z3SMTMemory() {

    class Z3NormalMemoryProxy<in Index : Z3BV>(val instance: Z3Memory<Index>) : Z3MemoryProxy<Index>() {
        override fun load(index: Index, elementSize: Int): Z3BV = instance.load(index, elementSize)
        override fun store(index: Index, element: Z3BV): Z3MemoryProxy<Index> = Z3NormalMemoryProxy(instance.store(index, element))
        override fun <T : Z3ValueExpr> store(index: Index, element: T): Z3MemoryProxy<Index> = Z3NormalMemoryProxy(instance.store(index, element))
        override fun get(index: Index): Byte_ = instance.get(index)
        override fun set(index: Index, value: Z3BV): Z3MemoryProxy<Index> = Z3NormalMemoryProxy(instance.set(index, value))
        override fun <T : Z3ValueExpr> set(index: Index, value: T): Z3MemoryProxy<Index> = Z3NormalMemoryProxy(instance.set(index, value))
    }

    class Z3UninterpretedMemoryProxy<in Index : Z3BV>(val instance: Z3MemoryOnIfStatements<Index>) : Z3MemoryProxy<Index>() {
        override fun load(index: Index, elementSize: Int): Z3BV = instance.load(index, elementSize)
        override fun store(index: Index, element: Z3BV): Z3MemoryProxy<Index> = Z3UninterpretedMemoryProxy(instance.store(index, element))
        override fun <T : Z3ValueExpr> store(index: Index, element: T): Z3MemoryProxy<Index> = Z3UninterpretedMemoryProxy(instance.store(index, element))
        override fun get(index: Index): Byte_ = instance.get(index)
        override fun set(index: Index, value: Z3BV): Z3MemoryProxy<Index> = Z3UninterpretedMemoryProxy(instance.set(index, value))
        override fun <T : Z3ValueExpr> set(index: Index, value: T): Z3MemoryProxy<Index> = Z3UninterpretedMemoryProxy(instance.set(index, value))
    }

    companion object {
        const val byteSize = 32

        enum class MemoryType {
            ARRAY, UF
        }

        var memoryType = MemoryType.ARRAY

        inline fun <reified T> withMemoryType(type: MemoryType, body: () -> T): T {
            val oldType = memoryType
            memoryType = type
            val result = body()
            memoryType = oldType
            return result
        }

        fun <Index : Z3BV> merge(default: Z3MemoryProxy<Index>, cases: List<Pair<Z3Bool, Z3MemoryProxy<Index>>>): Z3MemoryProxy<Index> {
            return when (default) {
                is Z3NormalMemoryProxy -> {
                    val casesInstance = cases.map { it.first to (it.second as Z3NormalMemoryProxy<Index>).instance }
                    Z3NormalMemoryProxy(Z3Memory.merge(default.instance, casesInstance))
                }
                is Z3UninterpretedMemoryProxy -> {
                    val casesInstance = cases.map { it.first to (it.second as Z3UninterpretedMemoryProxy<Index>).instance }
                    Z3UninterpretedMemoryProxy(Z3MemoryOnIfStatements.merge(default.instance, casesInstance))
                }
                else -> throw IllegalStateException("Too many inheritors")
            }
        }

        inline fun <reified Index : Z3BV> makeDefault(ctx: Context, name: String, default: Byte_) = when (memoryType) {
            MemoryType.ARRAY -> Z3NormalMemoryProxy<Index>(Z3Memory.makeDefault(ctx, name, default))
            MemoryType.UF -> Z3UninterpretedMemoryProxy<Index>(Z3MemoryOnIfStatements.makeDefault(ctx, name, default))
        }

        inline fun <reified Index : Z3BV> makeFree(ctx: Context, name: String) = when (memoryType) {
            MemoryType.ARRAY -> Z3NormalMemoryProxy<Index>(Z3Memory.makeFree(ctx, name))
            MemoryType.UF -> Z3UninterpretedMemoryProxy<Index>(Z3MemoryOnIfStatements.makeFree(ctx, name))
        }

        inline fun <reified Index : Z3BV> makeVar(ctx: Context, name: String) = when (memoryType) {
            MemoryType.ARRAY -> Z3NormalMemoryProxy<Index>(Z3Memory.makeVar(ctx, name))
            MemoryType.UF -> TODO()
        }
    }


    abstract fun load(index: Index, elementSize: Int): Z3BV

    inline fun <reified T : Z3ValueExpr> load(index: Index): T = when (this) {
        is Z3NormalMemoryProxy -> instance.load(index)
        is Z3UninterpretedMemoryProxy -> instance.load(index)
        else -> throw IllegalStateException("Too many inheritors")
    }

    abstract fun store(index: Index, element: Z3BV): Z3MemoryProxy<Index>
    abstract fun <T : Z3ValueExpr> store(index: Index, element: T): Z3MemoryProxy<Index>
    abstract operator fun get(index: Index): Byte_
    abstract operator fun set(index: Index, value: Z3BV): Z3MemoryProxy<Index>
    abstract operator fun <T : Z3ValueExpr> set(index: Index, value: T): Z3MemoryProxy<Index>
}

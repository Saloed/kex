package org.jetbrains.research.kex.smt.z3


import com.microsoft.z3.Context

private val engine = Z3Engine


abstract class Z3MemoryProxy<in Index : Z3BV> : Z3SMTMemory() {

    class Z3NormalMemoryProxy<in Index : Z3BV>(val instance: Z3Memory<Index>) : Z3MemoryProxy<Index>() {
        override fun load(index: Index, elementSize: Int): Z3BV = instance.load(index, elementSize)
        override fun store(index: Index, element: Z3BV): Z3MemoryProxy<Index> = Z3NormalMemoryProxy(instance.store(index, element))
        override fun <T : Z3ValueExpr> store(index: Index, element: T): Z3MemoryProxy<Index> = Z3NormalMemoryProxy(instance.store(index, element))
        override fun get(index: Index): Byte_ = instance.get(index)
        override fun set(index: Index, value: Z3BV): Z3MemoryProxy<Index> = Z3NormalMemoryProxy(instance.set(index, value))
        override fun <T : Z3ValueExpr> set(index: Index, value: T): Z3MemoryProxy<Index> = Z3NormalMemoryProxy(instance.set(index, value))
    }

    class Z3UninterpretedMemoryProxy<in Index : Z3BV>(val instance: Z3UninterpretedMemory<Index>) : Z3MemoryProxy<Index>() {
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
                    Z3UninterpretedMemoryProxy(Z3UninterpretedMemory.merge(default.instance, casesInstance))
                }
                else -> throw IllegalStateException("Too many inheritors")
            }
        }

        inline fun <reified Index : Z3BV> makeDefault(ctx: Context, name: String, default: Byte_) = when (memoryType) {
            MemoryType.ARRAY -> Z3NormalMemoryProxy<Index>(Z3Memory.makeDefault(ctx, name, default))
            MemoryType.UF -> Z3UninterpretedMemoryProxy<Index>(Z3UninterpretedMemory.makeDefault(ctx, name, default))
        }

        inline fun <reified Index : Z3BV> makeFree(ctx: Context, name: String) = when (memoryType) {
            MemoryType.ARRAY -> Z3NormalMemoryProxy<Index>(Z3Memory.makeFree(ctx, name))
            MemoryType.UF -> Z3UninterpretedMemoryProxy<Index>(Z3UninterpretedMemory.makeFree(ctx, name))
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


class Z3UninterpretedMemory<in Index : Z3BV>(
        val ctx: Context,
        val name: String,
        val default: Z3BV?,
        val stores: StoreTree<Z3BV>
) : Z3SMTMemory() {

    class StoreTree<Index : Z3BV>(val ctx: Context, val default: Z3BV?, val stores: List<Pair<Index, Z3BV>>, val children: List<Pair<Z3Bool, StoreTree<Index>>>) {
        fun storeExpression(index: Index, resultVar: Z3BV): Z3ValueExpr {
            val foldInitial: Z3ValueExpr = default?.let { resultVar eq it } ?: Z3Bool.makeConst(ctx, false)
            val nestedStore = children.foldRight(foldInitial) { (cond, memory), acc  ->
                `if`(cond, memory.storeExpression(index, resultVar), acc)
            }
            return stores.foldRight(nestedStore) { (idx, value), acc  ->
                `if`(index eq idx, resultVar eq value, acc)
            }
        }

        private fun `if`(cond: Z3ValueExpr, `true`: Z3ValueExpr, `false`: Z3ValueExpr): Z3ValueExpr{
            val axioms = spliceAxioms(ctx, `true`.axiom, `false`.axiom)
            val result = engine.ite(ctx, cond.expr, `true`.expr, `false`.expr)
            return Z3ValueExpr(ctx, result, axioms)
        }

        operator fun plus(store: Pair<Index, Z3BV>) = StoreTree(ctx, default, stores + store, children)
        fun merge(cases: List<Pair<Z3Bool, StoreTree<Index>>>) = StoreTree(ctx, default, stores, children + cases)

        companion object {
            fun <Index : Z3BV> empty(ctx: Context) = StoreTree<Index>(ctx, null, emptyList(), emptyList())
        }
    }


    companion object {
        const val byteSize = 32

        fun <Index : Z3BV> merge(default: Z3UninterpretedMemory<Index>, cases: List<Pair<Z3Bool, Z3UninterpretedMemory<Index>>>): Z3UninterpretedMemory<Index> {
            val newStore = default.stores.merge(cases.map { it.first to it.second.stores })
            return Z3UninterpretedMemory(default.ctx, default.name, default.default, newStore)
        }

        inline fun <reified Index : Z3BV> makeDefault(ctx: Context, name: String, default: Byte_) = Z3UninterpretedMemory<Index>(ctx, name, default, StoreTree.empty(ctx))

        inline fun <reified Index : Z3BV> makeFree(ctx: Context, name: String) = Z3UninterpretedMemory<Index>(ctx, name, null, StoreTree.empty(ctx))

    }

    inline fun <reified T : Z3ValueExpr> load(index: Index) = Z3ValueExpr.forceCast<T>(load(index, Z3ValueExpr.getStaticBitsize<T>(ctx)))

    fun load(index: Index, elementSize: Int): Z3BV {
        require(elementSize == byteSize) { "Element size $elementSize is not supported" }
        val result = Byte_.makeFreshVar(ctx, "${name}_load")
        val memoryStores = stores.storeExpression(index, result)
        return Z3BV(ctx, result.expr, memoryStores.asAxiom())
    }

    fun store(index: Index, element: Z3BV): Z3UninterpretedMemory<Index> {
        val elementSize = element.getBitsize()
        require(elementSize == byteSize) { "Element size $elementSize is not supported" }
        return Z3UninterpretedMemory(ctx, name, default, stores + (index to element))
    }

    fun <T : Z3ValueExpr> store(index: Index, element: T) = store(index, element.toBV())

    operator fun get(index: Index) = load<Byte_>(index)
    operator fun set(index: Index, value: Z3BV) = store(index, value)
    operator fun <T : Z3ValueExpr> set(index: Index, value: T) = store(index, value)

}

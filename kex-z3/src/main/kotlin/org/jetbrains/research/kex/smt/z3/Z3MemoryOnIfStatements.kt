package org.jetbrains.research.kex.smt.z3


import com.microsoft.z3.Context

private val engine = Z3Engine


class Z3MemoryOnIfStatements<in Index : Z3BV>(
        val ctx: Context,
        val name: String,
        val default: Z3BV?,
        val stores: StoreTree<Z3BV>
) : Z3SMTMemory() {

    class StoreTree<Index : Z3BV>(
            val ctx: Context,
            val default: Z3BV?,
            val stores: List<Pair<Index, Z3BV>>,
            val children: List<Pair<Z3Bool, StoreTree<Index>>>) {

        fun storeExpression(index: Index, resultVar: Z3BV): Z3ValueExpr {
            val foldInitial: Z3ValueExpr = default?.let { resultVar eq it }
                    ?: Z3Bool.makeConst(ctx, false)
            val nestedStore = children.foldRight(foldInitial) { (cond, memory), acc ->
                `if`(cond, memory.storeExpression(index, resultVar), acc)
            }
            return stores.foldRight(nestedStore) { (idx, value), acc ->
                `if`(index eq idx, resultVar eq value, acc)
            }
        }

        private fun `if`(cond: Z3ValueExpr, `true`: Z3ValueExpr, `false`: Z3ValueExpr): Z3ValueExpr {
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

        fun <Index : Z3BV> merge(default: Z3MemoryOnIfStatements<Index>, cases: List<Pair<Z3Bool, Z3MemoryOnIfStatements<Index>>>) = default.join(cases)

        inline fun <reified Index : Z3BV> makeDefault(ctx: Context, name: String, default: Byte_) = Z3MemoryOnIfStatements<Index>(ctx, name, default, StoreTree.empty(ctx))

        inline fun <reified Index : Z3BV> makeFree(ctx: Context, name: String) = Z3MemoryOnIfStatements<Index>(ctx, name, null, StoreTree.empty(ctx))

    }

    inline fun <reified T : Z3ValueExpr> load(index: Index) = Z3ValueExpr.forceCast<T>(load(index, Z3ValueExpr.getStaticBitsize<T>(ctx)))

    fun load(index: Index, elementSize: Int): Z3BV {
        require(elementSize == byteSize) { "Element size $elementSize is not supported" }
        val result = Byte_.makeFreshVar(ctx, "${name}_load")
        val memoryStore = stores.storeExpression(index, result)
        val axiom = memoryStore.asAxiom()
        if (axiom.simplify() == ctx.mkFalse()) {
            return Z3BV(ctx, result.expr)
        }
        return Z3BV(ctx, result.expr, axiom)
    }

    fun store(index: Index, element: Z3BV): Z3MemoryOnIfStatements<Index> {
        val elementSize = element.getBitsize()
        require(elementSize == byteSize) { "Element size $elementSize is not supported" }
        return fork(index to element)
    }

    fun <T : Z3ValueExpr> store(index: Index, element: T) = store(index, element.toBV())

    operator fun get(index: Index) = load<Byte_>(index)
    operator fun set(index: Index, value: Z3BV) = store(index, value)
    operator fun <T : Z3ValueExpr> set(index: Index, value: T) = store(index, value)

    fun fork(store: Pair<Index, Z3BV>): Z3MemoryOnIfStatements<Index> =
            Z3MemoryOnIfStatements(ctx, name, default, stores + store)

    fun <Index : Z3BV> join(cases: List<Pair<Z3Bool, Z3MemoryOnIfStatements<Index>>>): Z3MemoryOnIfStatements<Index> {
        val newStore = stores.merge(cases.map { it.first to it.second.stores })
        return Z3MemoryOnIfStatements(ctx, name, default, newStore)
    }

}

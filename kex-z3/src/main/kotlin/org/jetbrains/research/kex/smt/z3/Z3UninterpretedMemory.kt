package org.jetbrains.research.kex.smt.z3


import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.FuncDecl
import org.jetbrains.research.kex.smt.SMTEngine

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

    private fun createVar() = ctx.mkFreshFuncDecl(name, arrayOf(Byte_.getStaticSort(ctx)), Byte_.getStaticSort(ctx)).also {
        if(ctx is Z3FixpointSolver.DeclarationTrackingContext){
            val a = 3
//            val declaration = Z3FixpointSolver.DeclarationTrackingContext.Declaration("$it", )
//            ctx.declarations.add(declaration)
        }
    }

    class StoreTree<Index : Z3BV>(val ctx: Context, val stores: List<Pair<Index, Z3BV>>, val children: List<Pair<Z3Bool, StoreTree<Index>>>) {
        fun storeExpression(funcDecl: FuncDecl): Expr {
            val nestedStore = children.fold(ctx.mkTrue() as Expr) { acc, (cond, memory) ->
                engine.ite(ctx, cond.expr, acc, memory.storeExpression(funcDecl))
            }
            return stores.fold(nestedStore) { acc, (idx, value) ->
                engine.binary(ctx, SMTEngine.Opcode.EQ, funcDecl.apply(idx.expr), value.expr)
            }
        }

        operator fun plus(store: Pair<Index, Z3BV>) = StoreTree(ctx, stores + store, children)
        fun merge(cases: List<Pair<Z3Bool, StoreTree<Index>>>) = StoreTree(ctx, stores, children + cases)

        companion object {
            fun <Index : Z3BV> empty(ctx: Context) = StoreTree<Index>(ctx, emptyList(), emptyList())
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
        val memoryVar = createVar()
        val axiom = stores.storeExpression(memoryVar)
        return Z3BV(ctx, memoryVar.apply(index.expr), axiom)
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

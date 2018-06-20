package org.jetbrains.research.kex.smt

import com.microsoft.z3.Context
import org.jetbrains.research.kex.smt.z3.Z3Engine
import org.jetbrains.research.kex.util.Loggable
import org.jetbrains.research.kex.util.unreachable
import kotlin.reflect.KClass

abstract class SMTEngine<in Context_t : Any, Expr_t : Any, Sort_t : Any, Function_t : Any> : Loggable {
    companion object {
        const val shortWidth = 32
        const val intWidth = 32
        const val longWidth = 64

        const val floatWidth = 32
        const val doubleWidth = 64
    }

    enum class Opcode {
        EQ,
        NEQ,
        ADD,
        SUB,
        MUL,
        DIV,
        MOD,
        GT,
        GE,
        LT,
        LE,
        SHL,
        SHR,
        ASHR,
        AND,
        OR,
        XOR,
        IMPLIES,
        IFF,
        CONCAT
    }

    abstract fun getSort(ctx: Context_t, expr: Expr_t): Sort_t
    abstract fun getBoolSort(ctx: Context_t): Sort_t
    abstract fun getBVSort(ctx: Context_t, size: Int): Sort_t
    abstract fun getFPSort(ctx: Context_t, esize: Int, ssize: Int): Sort_t
    abstract fun getFloatSort(ctx: Context_t): Sort_t
    abstract fun getDoubleSort(ctx: Context_t): Sort_t
    abstract fun getArraySort(ctx: Context_t, domain: Sort_t, range: Sort_t): Sort_t
    abstract fun isBoolSort(ctx: Context_t, sort: Sort_t): Boolean
    abstract fun isBVSort(ctx: Context_t, sort: Sort_t): Boolean
    abstract fun isFPSort(ctx: Context_t, sort: Sort_t): Boolean
    abstract fun isArraySort(ctx: Context_t, sort: Sort_t): Boolean

    fun isBool(ctx: Context_t, expr: Expr_t) = isBoolSort(ctx, getSort(ctx, expr))
    fun isBV(ctx: Context_t, expr: Expr_t) = isBVSort(ctx, getSort(ctx, expr))
    fun isFP(ctx: Context_t, expr: Expr_t) = isFPSort(ctx, getSort(ctx, expr))
    fun isArray(ctx: Context_t, expr: Expr_t) = isArraySort(ctx, getSort(ctx, expr))
    abstract fun bvBitsize(ctx: Context_t, sort: Sort_t): Int
    abstract fun fpEBitsize(ctx: Context_t, sort: Sort_t): Int
    abstract fun fpSBitsize(ctx: Context_t, sort: Sort_t): Int

    abstract fun bool2bv(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t
    abstract fun bv2bool(ctx: Context_t, expr: Expr_t): Expr_t
    abstract fun bv2bv(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t
    abstract fun bv2float(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t
    abstract fun float2bv(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t
    abstract fun float2float(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t

    abstract fun hash(ctx: Context_t, expr: Expr_t): Int
    abstract fun name(ctx: Context_t, expr: Expr_t): String
    abstract fun toString(ctx: Context_t, expr: Expr_t): String

    abstract fun simplify(ctx: Context_t, expr: Expr_t): Expr_t
    abstract fun equality(ctx: Context_t, lhv: Expr_t, rhv: Expr_t): Boolean

    abstract fun makeVar(ctx: Context_t, sort: Sort_t, name: String, fresh: Boolean): Expr_t

    abstract fun makeBoolConst(ctx: Context_t, value: Boolean): Expr_t
    abstract fun makeNumericConst(ctx: Context_t, value: Short): Expr_t
    abstract fun makeNumericConst(ctx: Context_t, value: Int): Expr_t
    abstract fun makeNumericConst(ctx: Context_t, value: Long): Expr_t
    abstract fun makeNumericConst(ctx: Context_t, sort: Sort_t, value: Long): Expr_t
    abstract fun makeFPConst(ctx: Context_t, value: Int): Expr_t
    abstract fun makeFPConst(ctx: Context_t, value: Float): Expr_t
    abstract fun makeFPConst(ctx: Context_t, value: Double): Expr_t
    abstract fun makeArrayConst(ctx: Context_t, sort: Sort_t, expr: Expr_t): Expr_t
    abstract fun makeFunction(ctx: Context_t, name: String, retSort: Sort_t, args: List<Sort_t>): Function_t

    abstract fun apply(ctx: Context_t, f: Function_t, args: List<Expr_t>): Expr_t

    abstract fun negate(ctx: Context_t, expr: Expr_t): Expr_t
    abstract fun binary(ctx: Context_t, opcode: Opcode, lhv: Expr_t, rhv: Expr_t): Expr_t

    abstract fun conjunction(ctx: Context_t, vararg exprs: Expr_t): Expr_t

    abstract fun zext(ctx: Context_t, n: Int, expr: Expr_t): Expr_t
    abstract fun sext(ctx: Context_t, n: Int, expr: Expr_t): Expr_t

    abstract fun load(ctx: Context_t, array: Expr_t, index: Expr_t): Expr_t
    abstract fun store(ctx: Context_t, array: Expr_t, index: Expr_t, value: Expr_t): Expr_t

    abstract fun ite(ctx: Context_t, cond: Expr_t, lhv: Expr_t, rhv: Expr_t): Expr_t

    abstract fun extract(ctx: Context_t, bv: Expr_t, high: Int, low: Int): Expr_t
}

class SMTEngineProxy<in Context_t : Any, Expr_t : Any, Sort_t : Any, Function_t : Any>
    : SMTEngine<Context_t, Expr_t, Sort_t, Function_t>() {

    companion object {
        private val engines: Map<KClass<*>, KClass<*>> = mapOf(
                Context::class to Z3Engine::class
        )
    }

    private fun getEngineClass(ctx: Any) = engines.getValue(ctx::class)
    private fun getEngine(ctx: Context_t) = getEngineClass(ctx).objectInstance
            ?: unreachable { log.error("SMT engine ${getEngineClass(ctx)} does not have object instance") }

    private fun proxyMethod(`object`: Any, methodName: String, vararg parameters: Class<*>) =
            `object`.javaClass.getMethod(methodName, *parameters)
                    ?: unreachable { log.error("SMT engine ${getEngineClass(`object`)} does not contain method $methodName") }

    private fun proxyInvoke(ctx: Context_t, methodName: String, vararg args: Any): Any {
        val engine = getEngine(ctx)
        val method = proxyMethod(engine, methodName, *args.map { it::class.java }.toTypedArray())
        return method.invoke(engine, *args) ?: unreachable { log.error("$methodName invocation returned null") }
    }

    @Suppress("UNCHECKED_CAST")
    private fun <ResT> proxy(ctx: Context_t, methodName: String, vararg args: Any): ResT =
            proxyInvoke(ctx, methodName, *args) as? ResT
                    ?: unreachable { log.error("SMT engine returned incorrect type object") }

    private fun getMethodName() = Throwable().stackTrace.drop(1).first().methodName

    override fun getSort(ctx: Context_t, expr: Expr_t): Sort_t = proxy(ctx, getMethodName(), ctx, expr)
    override fun getBoolSort(ctx: Context_t): Sort_t = proxy(ctx, getMethodName(), ctx)
    override fun getBVSort(ctx: Context_t, size: Int): Sort_t = proxy(ctx, getMethodName(), ctx, size)
    override fun getFPSort(ctx: Context_t, esize: Int, ssize: Int): Sort_t = proxy(ctx, getMethodName(), ctx, esize, ssize)
    override fun getFloatSort(ctx: Context_t): Sort_t = proxy(ctx, getMethodName())
    override fun getDoubleSort(ctx: Context_t): Sort_t = proxy(ctx, getMethodName())
    override fun getArraySort(ctx: Context_t, domain: Sort_t, range: Sort_t): Sort_t = proxy(ctx, getMethodName(), ctx, domain, range)

    override fun bool2bv(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t = proxy(ctx, getMethodName(), expr, sort)
    override fun bv2bool(ctx: Context_t, expr: Expr_t): Expr_t = proxy(ctx, getMethodName(), expr)
    override fun bv2bv(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t = proxy(ctx, getMethodName(), expr, sort)
    override fun bv2float(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t = proxy(ctx, getMethodName(), expr, sort)
    override fun float2bv(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t = proxy(ctx, getMethodName(), expr, sort)
    override fun float2float(ctx: Context_t, expr: Expr_t, sort: Sort_t): Expr_t = proxy(ctx, getMethodName(), expr, sort)

    override fun isBoolSort(ctx: Context_t, sort: Sort_t): Boolean = proxy(ctx, getMethodName(), sort)
    override fun isBVSort(ctx: Context_t, sort: Sort_t): Boolean = proxy(ctx, getMethodName(), sort)
    override fun isFPSort(ctx: Context_t, sort: Sort_t): Boolean = proxy(ctx, getMethodName(), sort)
    override fun isArraySort(ctx: Context_t, sort: Sort_t): Boolean = proxy(ctx, getMethodName(), sort)
    override fun bvBitsize(ctx: Context_t, sort: Sort_t): Int = proxy(ctx, getMethodName(), sort)
    override fun fpEBitsize(ctx: Context_t, sort: Sort_t): Int = proxy(ctx, getMethodName(), sort)
    override fun fpSBitsize(ctx: Context_t, sort: Sort_t): Int = proxy(ctx, getMethodName(), sort)

    override fun hash(ctx: Context_t, expr: Expr_t): Int = proxy(ctx, getMethodName(), ctx, expr)
    override fun name(ctx: Context_t, expr: Expr_t): String = proxy(ctx, getMethodName(), ctx, expr)
    override fun toString(ctx: Context_t, expr: Expr_t): String = proxy(ctx, getMethodName(), ctx, expr)

    override fun simplify(ctx: Context_t, expr: Expr_t): Expr_t = proxy(ctx, getMethodName(), ctx, expr)

    override fun equality(ctx: Context_t, lhv: Expr_t, rhv: Expr_t): Boolean = proxy(ctx, getMethodName(), ctx, lhv, rhv)

    override fun makeVar(ctx: Context_t, sort: Sort_t, name: String, fresh: Boolean): Expr_t = proxy(ctx, getMethodName(), sort, name, fresh)

    override fun makeBoolConst(ctx: Context_t, value: Boolean): Expr_t = proxy(ctx, getMethodName(), ctx, value)

    override fun makeNumericConst(ctx: Context_t, value: Short): Expr_t = proxy(ctx, getMethodName(), value)

    override fun makeNumericConst(ctx: Context_t, value: Int): Expr_t = proxy(ctx, getMethodName(), value)
    override fun makeNumericConst(ctx: Context_t, value: Long): Expr_t = proxy(ctx, getMethodName(), value)
    override fun makeNumericConst(ctx: Context_t, sort: Sort_t, value: Long): Expr_t = proxy(ctx, getMethodName(), sort, value)
    override fun makeFPConst(ctx: Context_t, value: Int): Expr_t = proxy(ctx, getMethodName(), value)
    override fun makeFPConst(ctx: Context_t, value: Float): Expr_t = proxy(ctx, getMethodName(), value)
    override fun makeFPConst(ctx: Context_t, value: Double): Expr_t = proxy(ctx, getMethodName(), value)
    override fun makeArrayConst(ctx: Context_t, sort: Sort_t, expr: Expr_t): Expr_t = proxy(ctx, getMethodName(), sort, expr)
    override fun makeFunction(ctx: Context_t, name: String, retSort: Sort_t, args: List<Sort_t>): Function_t =
            proxy(ctx, getMethodName(), name, retSort, args)

    override fun apply(ctx: Context_t, f: Function_t, args: List<Expr_t>): Expr_t = proxy(ctx, getMethodName(), f, args)
    override fun negate(ctx: Context_t, expr: Expr_t): Expr_t = proxy(ctx, getMethodName(), expr)
    override fun binary(ctx: Context_t, opcode: Opcode, lhv: Expr_t, rhv: Expr_t): Expr_t = proxy(ctx, getMethodName(), opcode, lhv, rhv)
    override fun conjunction(ctx: Context_t, vararg exprs: Expr_t): Expr_t = proxy(ctx, getMethodName(), exprs)

    override fun zext(ctx: Context_t, n: Int, expr: Expr_t): Expr_t = proxy(ctx, getMethodName(), n, expr)
    override fun sext(ctx: Context_t, n: Int, expr: Expr_t): Expr_t = proxy(ctx, getMethodName(), n, expr)

    override fun load(ctx: Context_t, array: Expr_t, index: Expr_t): Expr_t = proxy(ctx, getMethodName(), array, index)
    override fun store(ctx: Context_t, array: Expr_t, index: Expr_t, value: Expr_t): Expr_t =
            proxy(ctx, getMethodName(), array, index, value)

    override fun ite(ctx: Context_t, cond: Expr_t, lhv: Expr_t, rhv: Expr_t): Expr_t =
            proxy(ctx, getMethodName(), cond, lhv, rhv)

    override fun extract(ctx: Context_t, bv: Expr_t, high: Int, low: Int): Expr_t =
            proxy(ctx, getMethodName(), bv, high, low)
}
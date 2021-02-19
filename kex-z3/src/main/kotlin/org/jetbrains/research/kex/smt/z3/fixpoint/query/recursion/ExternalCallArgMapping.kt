package org.jetbrains.research.kex.smt.z3.fixpoint.query.recursion

import com.microsoft.z3.Expr
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.SolverExpr_
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithCallMemory
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithRecursionSupport
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term

data class ExternalCallArgMapping(
    val owner: Term,
    val ownerExpr: Expr,
    val args: List<Pair<Term, Expr>>,
    val inMemory: List<Pair<MemoryDescriptor, Expr>>,
    val result: Term,
    val resultExpr: Expr,
    val outMemory: List<Pair<MemoryDescriptor, Expr>>
) {
    val termMap = mutableMapOf<Int, Term>()
    val exprMap = mutableMapOf<Int, Expr>()
    private val exprIdIdx = mutableMapOf<Int, Int>()
    private var exprIdx = 0

    init {
        termMap[ownerExpr.id] = owner
        exprMap[ownerExpr.id] = ownerExpr
        termMap[resultExpr.id] = result
        exprMap[resultExpr.id] = resultExpr
        args.forEach { (term, e) ->
            termMap[e.id] = term
            exprMap[e.id] = e
        }
    }

    fun mapVar(expr: SolverExpr_, type: KexType): Term {
        val exprId = expr.id
        val varTerm = term { value(type, "var_${exprIdIdx.getOrPut(exprId) { exprIdx++ }}") }
        termMap[exprId] = varTerm
        exprMap[exprId] = expr
        return varTerm
    }

    companion object {
        fun create(
            info: Z3ConverterWithRecursionSupport.ExternalCallArgumentsInfo,
            inArgs: Array<out Expr>,
            outArgs: Array<out Expr>,
            callInfo: Z3ConverterWithCallMemory.CallInfo
        ): ExternalCallArgMapping {
            val callTermProto = callInfo.predicate.callTerm
            val owner = term { value(callTermProto.owner.type, "owner") }
            val args = callTermProto.arguments.mapIndexed { i, arg -> term { arg(arg.type, i) } }
            val resultValueTerm = term { value(callInfo.resultTerm.type, "result") }
            val (inArgsExprs, inMemoryExprs) = inArgs.toList().split(info.inArgs, info.inMemories)
            val (outArgsExprs, outMemoryExprs) = outArgs.toList().split(info.outArgs, info.outMemories)
            val ownerExpr = inArgsExprs.first()
            val argsExprs = inArgsExprs.drop(1)
            val resultExpr = outArgsExprs.first()
            return ExternalCallArgMapping(
                owner, ownerExpr,
                args.zip(argsExprs),
                info.memoryDescriptors.zip(inMemoryExprs),
                resultValueTerm, resultExpr,
                info.memoryDescriptors.zip(outMemoryExprs)
            )
        }

        private fun <T> List<T>.split(vararg chunks: Int): List<List<T>> {
            check(chunks.sum() == size) { "Incorrect chunks sizes" }
            val result = mutableListOf<List<T>>()
            var index = 0
            for (chunk in chunks) {
                result += subList(index, index + chunk)
                index += chunk
            }
            return result
        }
    }
}

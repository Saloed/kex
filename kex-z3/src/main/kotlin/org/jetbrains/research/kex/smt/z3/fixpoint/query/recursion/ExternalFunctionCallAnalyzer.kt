package org.jetbrains.research.kex.smt.z3.fixpoint.query.recursion

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.Expr
import com.microsoft.z3.FunctionCallAnalyzer
import com.microsoft.z3.enumerations.Z3_decl_kind
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.Dynamic_
import org.jetbrains.research.kex.smt.z3.ExprFactory_
import org.jetbrains.research.kex.smt.z3.SolverExpr_
import org.jetbrains.research.kex.smt.z3.Z3EngineContext
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointCallCtx
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.ExprFactoryWithKnownExprs
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ContextWithMemoryArrays
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithCallMemory
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithRecursionSupport
import org.jetbrains.research.kex.smt.z3.fixpoint.model.FixpointModelConverter
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.ValueTerm
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.Transformer

class ExternalFunctionCallAnalyzer(
    val ctx: FixpointCallCtx,
    val declarationMapping: ModelDeclarationMapping,
    val argsInfo: Map<Int, Z3ConverterWithRecursionSupport.ExternalCallArgumentsInfo>,
    val externalCallResolver: (RecoveredModel) -> PredicateState?
) : FunctionCallAnalyzer {
    private var callIdx = 0
    private val eCtx: Z3EngineContext
        get() = ctx.ef.ctx

    private val Expr.isFunctionCall
        get() = funcDecl.declKind == Z3_decl_kind.Z3_OP_FUNCTION_CALL

    override fun analyze(
        functionId: Int,
        expression: Expr,
        inArgs: Array<out Expr>,
        outArgs: Array<out Expr>
    ): Expr? {
        callIdx++
        val result = try {
            when {
                expression.isFunctionCall -> analyzeFunctionCall(functionId, expression, inArgs, outArgs)
                else -> analyzeOtherExpr(functionId, expression, inArgs, outArgs)
            }
        } catch (ex: Throwable) {
            log.error(ex.message, ex.cause)
            null
        }
        log.debug("$expression | ${inArgs.contentToString()} | ${outArgs.contentToString()}\n=>\n$result")
        log.debug("--------------------------------------------------------------------")
        return result
    }

    private fun analyzeFunctionCall(
        functionId: Int,
        expression: Expr,
        inArgs: Array<out Expr>,
        outArgs: Array<out Expr>
    ): Expr? {
        if (outArgs.all { it.isConst } && inArgs.all { it.isConst }) return eCtx.mkTrue()
        error("Function call with non constant args")
    }

    private fun analyzeOtherExpr(
        functionId: Int,
        expression: Expr,
        inArgs: Array<out Expr>,
        outArgs: Array<out Expr>
    ): Expr? {
        val callPrototype = declarationMapping.calls[functionId] ?: error("Unknown call $functionId")
        val callArgs = argsInfo[functionId] ?: error("Unknown call $functionId")
        val argMapping =
            ExternalCallArgMapping.create(callArgs, inArgs, outArgs, callPrototype)
        val call = mkCall(callPrototype.predicate, argMapping)
        val callQuery = convertQueryExpressionToPS(argMapping, expression, callPrototype, call)
        val resultPs = resolveCallQuery(callQuery) ?: return null
        val resultExpr = convertResultPsToExpr(argMapping, resultPs)
        return resultExpr.simplify()
    }

    private fun resolveCallQuery(query: RecoveredModel): PredicateState? {
        val result = externalCallResolver(query)
        log.debug("$query\n=>\n$result")
        log.debug("*************************************************************")
        return result
    }

    private fun convertResultPsToExpr(
        argMapping: ExternalCallArgMapping,
        resultPs: PredicateState
    ): SolverExpr_ {
        val argsName2Expr = argMapping.termMap.map { it.value.name to it.key }.toMap()
            .mapValues { argMapping.exprMap[it.value] }
        val ps = UniqueTermGenerator(argsName2Expr.keys, "$callIdx").apply(resultPs)
        val convertEf = ExprFactoryWithKnownExprs(eCtx) { type: KexType, name: String ->
            argsName2Expr[name]?.let { Dynamic_.forceCast(Dynamic_(eCtx, it), ExprFactory_.getType(type)) }
        }
        val convertCtx = Z3ContextWithMemoryArrays(convertEf)
        convertCtx.setUpInitialMemory(eCtx, argMapping.inMemory.toMap())
        convertCtx.resetMemory()
        val result = ctx.converter.convert(ps, convertEf, convertCtx)
        return result.asAxiom()
    }

    private class UniqueTermGenerator(private val knownTerms: Set<String>, private val postfix: String) :
        Transformer<UniqueTermGenerator> {
        private val mapping = mutableMapOf<ValueTerm, ValueTerm>()
        override fun transformValueTerm(term: ValueTerm): Term {
            if (term.name in knownTerms) return term
            return mapping.getOrPut(term) {
                term { value(term.type, "${term.name}_$postfix") } as ValueTerm
            }
        }
    }

    private fun convertQueryExpressionToPS(
        argMapping: ExternalCallArgMapping,
        expression: Expr,
        info: Z3ConverterWithCallMemory.CallInfo,
        call: CallPredicate
    ): RecoveredModel {
        val mapping =
            ExternalCallDeclarationMapping(declarationMapping, argMapping, info.index, call)
        val converter = FixpointModelConverter(mapping, ctx.tf, ctx.z3Context)
        return converter.apply(expression.simplify())
    }

    private fun mkCall(prototype: CallPredicate, argMapping: ExternalCallArgMapping): CallPredicate {
        val call = CallTerm(
            prototype.callTerm.type,
            argMapping.owner,
            prototype.callTerm.method,
            prototype.callTerm.instruction,
            argMapping.args.map { it.first },
            MemoryVersion.initial().resetToVersion(0)
        )
        return CallPredicate(argMapping.result, call)
    }
}

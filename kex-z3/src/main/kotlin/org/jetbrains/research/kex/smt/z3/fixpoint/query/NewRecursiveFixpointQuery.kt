package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import com.microsoft.z3.FunctionCallAnalyzer
import com.microsoft.z3.enumerations.Z3_decl_kind
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.Dynamic_
import org.jetbrains.research.kex.smt.z3.ExprFactory_
import org.jetbrains.research.kex.smt.z3.SolverExpr_
import org.jetbrains.research.kex.smt.z3.Z3EngineContext
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointCallCtx
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointCallCtxWithFunctionCalls
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.ExprFactoryWithKnownExprs
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ContextWithMemoryArrays
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithCallMemory
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithRecursionSupport
import org.jetbrains.research.kex.smt.z3.fixpoint.model.FixpointModelConverter
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.model.TermDependency
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kfg.type.TypeFactory

class NewRecursiveFixpointQuery(
    val state: PredicateState,
    val initialPath: PredicateState,
    val positivePath: PredicateState,
    val query: PredicateState,
    val memoryVersionInfo: MemoryVersionInfo,
    val recursiveCallPredicates: Set<CallPredicate>,
    val externalCallResolver: (RecoveredModel) -> PredicateStateWithPath?
) : FixpointSolverQuery() {

    private val hasExternalFunctionCalls by lazy {
        PredicateCollector.collectIsInstance<CallPredicate>(state)
            .any { it !in recursiveCallPredicates }
    }

    override fun mkContext(tf: TypeFactory) = when {
        hasExternalFunctionCalls -> FixpointCallCtxWithFunctionCalls(tf, this)
        else -> super.mkContext(tf)
    }

    private val recursionPredicate = Z3FixpointSolver.Predicate(0)
    override val FixpointCallCtx.psConverter: Z3ConverterWithRecursionSupport
        get() = converter as Z3ConverterWithRecursionSupport

    override fun makeConverter(tf: TypeFactory) =
        Z3ConverterWithRecursionSupport(tf, memoryVersionInfo, recursiveCallPredicates, recursionPredicate)

    override fun allStatesForMemoryInitialization() = listOf(state, query, positivePath, initialPath)
    override fun makeQuery(ctx: FixpointCallCtx): FixpointSolverCall {
        val z3State = ctx.build {
            convert(state).asAxiom() as BoolExpr
        }
        val rootPredicate = ctx.psConverter.buildRootPredicateApp(ctx.declarationTracker, ctx.ef, ctx.z3Context)

        val z3Initial = ctx.build {
            convert(initialPath).asAxiom() as BoolExpr
        }

        val z3positive = ctx.build {
            convert(positivePath).asAxiom() as BoolExpr
        }
        val z3query = ctx.build {
            convert(query).asAxiom() as BoolExpr
        }

        val calls = ctx.psConverter.getCallsInfo()
        val declarationExprs = ctx.knownDeclarations.map { it.expr }
        val declarationMapping = ModelDeclarationMapping.create(
            rootPredicate.arguments, memoryVersionInfo,
            state, positivePath, query, initialPath
        )
        declarationMapping.initializeCalls(calls)

        if (hasExternalFunctionCalls) {
            initializeFunctionCallAnalyzer(ctx, declarationMapping)
        }

        return FixpointSolverCall(
            listOf(recursionPredicate),
            declarationMapping,
            object : StatementBuilder(ctx, z3State, declarationExprs) {
                override val definePredicateApps = false
                override fun complicatedPredicates() = listOf(rootPredicate.predicate.asAxiom() as BoolExpr)
                override fun StatementOperation.positiveStatement(): List<BoolExpr> {
                    val init = ctx.build {
                        val statement = (getState() and z3Initial) implies getComplicatedPredicate(0)
                        statement.forall(declarations).typedSimplify()
                    }

                    val statement = ctx.build {
                        val statement = (getState() and z3positive) implies getComplicatedPredicate(0)
                        statement.forall(declarations).typedSimplify()
                    }
                    return listOf(init, statement)
                }

                override fun StatementOperation.queryStatement() = ctx.build {
                    val statement = (getState() and z3query and getComplicatedPredicate(0)) implies context.mkFalse()
                    statement.forall(declarations).typedSimplify()
                }
            })
    }

    private fun initializeFunctionCallAnalyzer(ctx: FixpointCallCtx, declarationMapping: ModelDeclarationMapping) {
        val externalFunctionCalls = ctx.psConverter.externalFunctionsInfo
        with(ctx.ef.ctx) {
            registerFunctionCallAnalyzer(
                ExternalFunctionCallAnalyzer(
                    ctx,
                    declarationMapping,
                    externalFunctionCalls,
                    externalCallResolver
                )
            )
            provideFunctionCallInfo(externalFunctionCalls.values.toTypedArray())
        }
    }

    class ExternalFunctionCallAnalyzer(
        val ctx: FixpointCallCtx,
        val declarationMapping: ModelDeclarationMapping,
        val argsInfo: Map<Int, Z3ConverterWithRecursionSupport.ExternalCallArgumentsInfo>,
        val externalCallResolver: (RecoveredModel) -> PredicateStateWithPath?
    ) : FunctionCallAnalyzer {

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
            val result = when {
                expression.isFunctionCall -> analyzeFunctionCall(functionId, expression, inArgs, outArgs)
                else -> analyzeOtherExpr(functionId, expression, inArgs, outArgs)
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
            val argMapping = ExternalCallArgMapping.create(callArgs, inArgs, outArgs, callPrototype)
            val call = mkCall(callPrototype.predicate, argMapping)
            val callQuery = convertQueryExpressionToPS(argMapping, expression, callPrototype, call)
            val resultPs = resolveCallQuery(callQuery) ?: return null
            val resultExpr = convertResultPsToExpr(argMapping, resultPs)
            return resultExpr.simplify()
        }

        private fun resolveCallQuery(query: RecoveredModel): PredicateState? {
            val result = externalCallResolver(query)?.toPredicateState()
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
            val convertEf = ExprFactoryWithKnownExprs(eCtx) { type: KexType, name: String ->
                argsName2Expr[name]?.let { Dynamic_.forceCast(Dynamic_(eCtx, it), ExprFactory_.getType(type)) }
            }
            val convertCtx = Z3ContextWithMemoryArrays(convertEf)
            convertCtx.setUpInitialMemory(eCtx, argMapping.inMemory.toMap())
            convertCtx.resetMemory()
            val result = ctx.converter.convert(resultPs, convertEf, convertCtx)
            return result.asAxiom()
        }

        private fun convertQueryExpressionToPS(
            argMapping: ExternalCallArgMapping,
            expression: Expr,
            info: Z3ConverterWithCallMemory.CallInfo,
            call: CallPredicate
        ): RecoveredModel {
            val mapping = ExternalCallDeclarationMapping(declarationMapping, argMapping, info.index, call)
            val converter = FixpointModelConverter(mapping, ctx.tf, ctx.z3Context)
            return converter.apply(expression)
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

    class ExternalCallDeclarationMapping(
        declarationMapping: ModelDeclarationMapping,
        val argMapping: ExternalCallArgMapping,
        val callIndex: Int,
        val callPredicate: CallPredicate
    ) : ModelDeclarationMapping(declarationMapping.arguments) {
        init {
            terms.putAll(declarationMapping.terms)
            callDependentDeclarations.putAll(declarationMapping.callDependentDeclarations)
            calls.putAll(declarationMapping.calls)
        }

        override fun getConst(expr: SolverExpr_, type: KexType, callDependencies: MutableSet<TermDependency>): Term {
            val term = argMapping.termMap[expr.id] ?: argMapping.mapVar(expr, type)
            if (term == argMapping.result) {
                callDependencies.add(TermDependency.CallResultDependency(term, callIndex, callPredicate))
            }
            return term
        }

    }


}

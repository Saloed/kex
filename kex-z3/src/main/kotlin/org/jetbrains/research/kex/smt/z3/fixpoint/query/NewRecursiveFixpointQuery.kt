package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointCallCtx
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointCallCtxWithFunctionCalls
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithRecursionSupport
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.query.recursion.ExternalFunctionCallAnalyzer
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kfg.type.TypeFactory

class NewRecursiveFixpointQuery(
    val state: PredicateState,
    val initialPath: PredicateState,
    val positivePath: PredicateState,
    val query: PredicateState,
    val memoryVersionInfo: MemoryVersionInfo,
    val recursiveCallPredicates: Set<CallPredicate>,
    val externalCallResolver: (RecoveredModel) -> PredicateState?
) : FixpointSolverQuery() {

    private val hasExternalFunctionCalls by lazy {
        PredicateCollector.collectIsInstance<CallPredicate>(state)
            .any { it !in recursiveCallPredicates }
    }

    override fun mkContext(tf: TypeFactory) =
        FixpointCallCtxWithFunctionCalls(tf, this, enableFunctionCalls = hasExternalFunctionCalls)

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
}

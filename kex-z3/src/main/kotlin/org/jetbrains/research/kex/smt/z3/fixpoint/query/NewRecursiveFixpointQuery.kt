package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithRecursionSupport
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kfg.type.TypeFactory

class NewRecursiveFixpointQuery(
        val state: PredicateState,
        val positivePath: PredicateState,
        val query: PredicateState,
        val memoryVersionInfo: MemoryVersionInfo,
        val recursiveCallPredicates: Set<CallPredicate>
) : FixpointSolverQuery() {
    private val recursionPredicate = Z3FixpointSolver.Predicate(0)
    private val recursionPathPredicate = Z3FixpointSolver.Predicate(1)
    override val Z3FixpointSolver.CallCtx.psConverter: Z3ConverterWithRecursionSupport
        get() = converter as Z3ConverterWithRecursionSupport

    override fun makeConverter(tf: TypeFactory) = Z3ConverterWithRecursionSupport(tf, memoryVersionInfo, recursiveCallPredicates, recursionPredicate, recursionPathPredicate)
    override fun allStatesForMemoryInitialization() = listOf(state, query, positivePath)
    override fun makeQuery(ctx: Z3FixpointSolver.CallCtx): FixpointSolverCall {
        val z3State = ctx.build {
            convert(state).asAxiom() as BoolExpr
        }
        val rootPredicate = ctx.psConverter.buildRootPredicateApp(ctx.declarationTracker, ctx.ef, ctx.z3Context)

        val z3positive = ctx.build {
            convert(positivePath).asAxiom() as BoolExpr
        }
        val z3query = ctx.build {
            convert(query).asAxiom() as BoolExpr
        }
        val rootPathPredicate = ctx.psConverter.buildRootPathPredicateApp(ctx.declarationTracker, ctx.ef, ctx.z3Context)

        val calls = ctx.psConverter.getCallsInfo()
        val declarationExprs = ctx.knownDeclarations.map { it.expr }
        val declarationMapping = ModelDeclarationMapping.create(
                rootPredicate.arguments, memoryVersionInfo,
                state, positivePath, query
        )
        declarationMapping.initializeCalls(calls)

        return FixpointSolverCall(listOf(recursionPredicate, recursionPathPredicate), declarationMapping,
                object : StatementBuilder(ctx, z3State, declarationExprs) {
                    override val definePredicateApps = false
                    override fun complicatedPredicates() = listOf(
                            rootPredicate.predicate.asAxiom() as BoolExpr,
                            rootPathPredicate.predicate.asAxiom() as BoolExpr
                    )

                    override fun StatementOperation.positiveStatement(): List<BoolExpr> {
                        val statement = ctx.build {
                            val statement = (getState() and z3positive) implies getComplicatedPredicate(0)
                            statement.forall(declarations).typedSimplify()
                        }
                        return listOf(statement)
                    }

                    override fun StatementOperation.queryStatement() = ctx.build {
                        val statement = (getState() and z3query and getComplicatedPredicate(0)) implies context.mkFalse()
                        statement.forall(declarations).typedSimplify()
                    }
                })
    }
}

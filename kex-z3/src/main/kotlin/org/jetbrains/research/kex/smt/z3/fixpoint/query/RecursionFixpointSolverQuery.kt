package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.smt.z3.fixpoint.UnknownCallsProcessor
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithRecursion
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.FieldLoadTerm
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.type.TypeFactory

class RecursionFixpointSolverQuery(
        val state: PredicateState,
        val recursiveCalls: Map<CallPredicate, Map<Field, FieldLoadTerm>>,
        val rootCall: CallPredicate,
        val recursionPath: PredicateState,
        val positive: PredicateState,
        val query: PredicateState
) : FixpointSolverQuery() {
    private val recursionPredicate = Z3FixpointSolver.Predicate(0)
    override fun allStatesForMemoryInitialization() = listOf(state, positive, query, recursionPath)
    override fun makeConverter(tf: TypeFactory) = Z3ConverterWithRecursion(recursiveCalls, rootCall, recursionPredicate.name, tf)
    override val Z3FixpointSolver.CallCtx.psConverter: Z3ConverterWithRecursion
        get() = converter as Z3ConverterWithRecursion

    override fun makeQuery(ctx: Z3FixpointSolver.CallCtx): FixpointSolverCall {
        val unknownCallsProcessor = UnknownCallsProcessor(ignore = recursiveCalls.keys, replaceWithArray = false) + state + recursionPath + positive + query
        if (unknownCallsProcessor.hasUnknownCalls()) throw IllegalArgumentException("Recursive with unknowns")

        val rootPredicate = ctx.psConverter.buildPredicate(rootCall, ctx.ef, ctx.z3Context).expr as BoolExpr

        val z3State = ctx.build {
            convert(state).asAxiom() as BoolExpr
        }
        val z3Recursion = ctx.build {
            convert(recursionPath).asAxiom() as BoolExpr
        }
        val z3Positive = ctx.build {
            val path = convert(positive).asAxiom() as BoolExpr
            path or z3Recursion
        }
        val z3Query = ctx.build {
            val path = convert(query).asAxiom() as BoolExpr
            path and z3Recursion.not()
        }

        val declarationExprs = ctx.knownDeclarations.map { it.expr }

        return FixpointSolverCall(listOf(recursionPredicate), ctx.psConverter.mapper, object : StatementBuilder(z3State, declarationExprs) {
            override fun StatementOperation.positiveStatement(): List<BoolExpr> {
                val statement = ctx.build {
                    val statement = (getState() and z3Positive) implies rootPredicate
                    statement.forall(declarations).optimize()
                }
                return listOf(statement)
            }

            override fun StatementOperation.queryStatement() = ctx.build {
                val statement = (getState() and z3Query and rootPredicate) implies context.mkFalse()
                statement.forall(declarations).optimize()
            }
        })
    }
}

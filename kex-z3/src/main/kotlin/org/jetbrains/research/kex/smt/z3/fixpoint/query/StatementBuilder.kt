package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import com.microsoft.z3.Solver
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations

interface StatementOperation {
    fun getState(): BoolExpr
    fun applyPredicate(ctx: Z3FixpointSolver.CallCtx, predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations): BoolExpr
}

class NormalStatementOperation(private val state: BoolExpr) : StatementOperation {
    override fun getState() = state
    override fun applyPredicate(ctx: Z3FixpointSolver.CallCtx, predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations) =
            predicate.call(ctx, arguments)
}

class DebugStatementOperation(
        private val state: BoolExpr,
        private val declarations: List<Expr>
) : StatementOperation {
    override fun getState(): BoolExpr {

        TODO("Not yet implemented")
    }

    override fun applyPredicate(ctx: Z3FixpointSolver.CallCtx, predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations): BoolExpr {
        TODO("Not yet implemented")
    }
}

abstract class StatementBuilder(private val stateInternal: BoolExpr, val declarations: List<Expr>) {
    abstract fun StatementOperation.positiveStatement(): List<BoolExpr>
    abstract fun StatementOperation.queryStatement(): BoolExpr

    fun normal() = StatementBuilderExecutor(NormalStatementOperation(stateInternal), this)
    fun debug() = StatementBuilderExecutor(DebugStatementOperation(stateInternal, declarations), this)
}

class StatementBuilderExecutor(val statementOp: StatementOperation, val stateOp: StatementBuilder) {
    fun positiveStatements() = stateOp.run {
        statementOp.positiveStatement()
    }

    fun queryStatement() = stateOp.run {
        statementOp.queryStatement()
    }

    fun makeAsserts(solver: Solver) {
        for (statement in positiveStatements()) {
            solver.add(statement)
        }
        solver.add(queryStatement())
    }
}


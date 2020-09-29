package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.microsoft.z3.*
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations

interface StatementOperation {
    fun getState(): BoolExpr
    fun applyPredicate(predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations): BoolExpr
}

class NormalStatementOperation(private val ctx: Z3FixpointSolver.CallCtx, private val state: BoolExpr) : StatementOperation {
    override fun getState() = state
    override fun applyPredicate(predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations) =
            predicate.call(ctx, arguments)
}

class DebugStatementOperation(
        private val ctx: Z3FixpointSolver.CallCtx,
        private val state: BoolExpr,
        private val declarations: List<Expr>
) : StatementOperation {
    private val stateDeclaration by lazy {
        val argSorts = declarations.map { it.sort }.toTypedArray()
        ctx.context.mkFuncDecl("state_predicate", argSorts, ctx.context.mkBoolSort())
    }
    private val predicateAppBindings = arrayListOf<Triple<FuncDecl, Z3FixpointSolver.Predicate, ArgumentDeclarations>>()
    private val predicateAppDeclarations = hashMapOf<String, FuncDecl>()

    override fun getState() =
            ctx.context.mkApp(stateDeclaration, *declarations.toTypedArray()) as BoolExpr

    override fun applyPredicate(predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations): BoolExpr {
        val declaration = predicateAppDeclarations.getOrPut(predicate.name) {
            val argSorts = declarations.map { it.sort }.toTypedArray()
            val decl = ctx.context.mkFuncDecl("${predicate.name}_app", argSorts, ctx.context.mkBoolSort())
            predicateAppBindings += Triple(decl, predicate, arguments)
            decl
        }
        return ctx.context.mkApp(declaration, *declarations.toTypedArray()) as BoolExpr
    }

    fun predicatesSmtLibDefinition() = predicateAppBindings.map { (decl, predicate, args) ->
        val predicateApp = predicate.call(ctx, args)
        "${predicateApp.funcDecl}\n${defineFun(decl, predicateApp)}"
    }

    fun stateSmtLibDefinition() = defineFun(stateDeclaration, state)

    private fun defineFun(decl: FuncDecl, body: BoolExpr): String {
        val forall = ctx.build { body.forall(declarations) } as Quantifier
        val sortedVars = forall.boundVariableNames.zip(forall.boundVariableSorts)
                .joinToString(separator = " ") { (name, sort) -> "($name $sort)" }
        return "(define-fun ${decl.name} (${sortedVars}) ${decl.range} ${body})"
    }
}

abstract class StatementBuilder(private val ctx: Z3FixpointSolver.CallCtx, private val stateInternal: BoolExpr, val declarations: List<Expr>) {
    abstract fun StatementOperation.positiveStatement(): List<BoolExpr>
    abstract fun StatementOperation.queryStatement(): BoolExpr

    fun normal() = StatementBuilderExecutor(NormalStatementOperation(ctx, stateInternal), this)
    fun debug() = StatementBuilderExecutor(DebugStatementOperation(ctx, stateInternal, declarations), this)
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

    fun debugSmtLib(): String {
        if (statementOp !is DebugStatementOperation) error("Debug SmtLib printing requires debug statement op")
        val statements = positiveStatements() + queryStatement()
        val predicatesDefinition = statementOp.predicatesSmtLibDefinition()
        val stateDefinition = statementOp.stateSmtLibDefinition()
        val asserts = statements.map { "(assert $it)" }
        val lines = predicatesDefinition + listOf(stateDefinition) + asserts
        return lines.joinToString("\n")
    }
}


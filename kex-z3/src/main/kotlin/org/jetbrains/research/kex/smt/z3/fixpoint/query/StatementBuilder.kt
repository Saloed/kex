package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.microsoft.z3.*
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations

interface StatementOperation {
    fun getState(): BoolExpr
    fun applyPredicate(predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations): BoolExpr
    fun getComplicatedPredicate(idx: Int): BoolExpr
}

class NormalStatementOperation(
        private val ctx: Z3FixpointSolver.CallCtx,
        private val state: BoolExpr,
        private val complicatedPredicates: List<BoolExpr>
) : StatementOperation {
    override fun getState() = state
    override fun applyPredicate(predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations) =
            predicate.call(ctx, arguments)

    override fun getComplicatedPredicate(idx: Int) = complicatedPredicates[idx]
}

class DebugStatementOperation(
        private val ctx: Z3FixpointSolver.CallCtx,
        private val state: BoolExpr,
        private val declarations: List<Expr>,
        private val complicatedPredicates: List<BoolExpr>,
        private val definePredicateApps: Boolean
) : StatementOperation {
    private val stateDeclaration by lazy {
        val argSorts = declarations.map { it.sort }.toTypedArray()
        ctx.context.mkFuncDecl("state_predicate", argSorts, ctx.context.mkBoolSort())
    }

    private val predicateAppDeclarations = hashMapOf<String, FuncDecl>()
    private val predicatesToDefine = hashSetOf<FuncDecl>()
    private val predicateBindings = arrayListOf<Pair<FuncDecl, BoolExpr>>()

    override fun getState() =
            ctx.context.mkApp(stateDeclaration, *declarations.toTypedArray()) as BoolExpr

    override fun applyPredicate(predicate: Z3FixpointSolver.Predicate, arguments: ArgumentDeclarations) =
            wrapPredicateApp(predicate.call(ctx, arguments), predicate.name)

    override fun getComplicatedPredicate(idx: Int) =
            wrapPredicateApp(complicatedPredicates[idx], "${complicatedPredicates[idx].funcDecl.name}")

    private fun wrapPredicateApp(predicateApp: BoolExpr, name: String): BoolExpr {
        predicatesToDefine += predicateApp.funcDecl
        if (!definePredicateApps) return predicateApp
        val declaration = predicateAppDeclarations.getOrPut(name) {
            val argSorts = declarations.map { it.sort }.toTypedArray()
            ctx.context.mkFuncDecl("${name}_app", argSorts, ctx.context.mkBoolSort())
        }
        predicateBindings += declaration to predicateApp
        return ctx.context.mkApp(declaration, *declarations.toTypedArray()) as BoolExpr
    }

    fun predicatesSmtLibDefinition(): List<String> {
        val predicateDecls = predicatesToDefine.map { "$it" }
        val bindingDefs = predicateBindings.map { (decl, predicateApp) -> defineFun(decl, predicateApp) }
        return predicateDecls + bindingDefs
    }

    fun stateSmtLibDefinition() = defineFun(stateDeclaration, state)

    private fun defineFun(decl: FuncDecl, body: BoolExpr): String {
        val forall = ctx.build { ctx.context.mkTrue().forall(declarations) } as Quantifier
        val sortedVars = "$forall".removePrefix("(forall").removeSuffix("(! true :weight 0))")
        return "(define-fun ${decl.name} $sortedVars ${decl.range} ${body.simplify()})"
    }
}

abstract class StatementBuilder(private val ctx: Z3FixpointSolver.CallCtx, private val stateInternal: BoolExpr, val declarations: List<Expr>) {
    open fun complicatedPredicates() = emptyList<BoolExpr>()
    open val definePredicateApps = true
    abstract fun StatementOperation.positiveStatement(): List<BoolExpr>
    abstract fun StatementOperation.queryStatement(): BoolExpr

    fun normal() = StatementBuilderExecutor(NormalStatementOperation(ctx, stateInternal, complicatedPredicates()), this)
    fun debug() = StatementBuilderExecutor(DebugStatementOperation(ctx, stateInternal, declarations, complicatedPredicates(), definePredicateApps), this)
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


package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.*
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kfg.type.TypeFactory

class Z3FixpointSolver(val tf: TypeFactory) {

    private class DeclarationTrackingContext: Context(){
        data class Declaration(val name: String, val sort: Sort, val expr: Expr)
        val declarations = hashSetOf<Declaration>()

        override fun mkConst(p0: String?, p1: Sort?) = super.mkConst(p0, p1).apply {
            declarations.add(Declaration("$this", sort, this))
        }

        override fun mkFreshConst(p0: String?, p1: Sort?) = super.mkFreshConst(p0, p1).apply {
            declarations.add(Declaration("$this", sort, this))
        }

    }

    private class DeclarationTrackingExprFactory: Z3ExprFactory(){
        override val ctx = DeclarationTrackingContext()
    }

    private class CallCtx(tf: TypeFactory) {
        val ef = DeclarationTrackingExprFactory()
        val context = ef.ctx
        val z3Context = Z3Context(ef, (1 shl 8) + 1, (1 shl 24) + 1)
        val converter = Z3Converter(tf)
        val solver: Solver
            get() = buildTactics().solver
                    ?: throw IllegalStateException("Unable to build solver")
        val fixpointSolver: Solver
            get() = context.mkSolver("HORN")
                    .apply {
                        val params = context.mkParams()
                        params.add("fp.engine", "spacer")
                        setParameters(params)
                    }
                    ?: throw IllegalStateException("Unable to build solver")

        fun convert(ps: PredicateState): Bool_ = converter.convert(ps, ef, z3Context).simplify()

        private fun buildTactics(): Tactic {
            Z3Params.load().forEach { (name, value) ->
                Global.setParameter(name, value.toString())
            }

            val ctx = ef.ctx
            val tactic = Z3Tactics.load().map {
                val tactic = ctx.mkTactic(it.type)
                val params = ctx.mkParams()
                it.params.forEach { (name, value) ->
                    when (value) {
                        is Value.BoolValue -> params.add(name, value.value)
                        is Value.IntValue -> params.add(name, value.value)
                        is Value.DoubleValue -> params.add(name, value.value)
                        is Value.StringValue -> params.add(name, value.value)
                    }
                }
                ctx.with(tactic, params)
            }.reduce { a, b -> ctx.andThen(a, b) }
            return ctx.tryFor(tactic, 10 * 1000)
        }

        fun build(builder: CallCtx.() -> BoolExpr) = builder()
        inline fun <reified T> withSolver(fixpoint: Boolean = false, query: Solver.() -> T) = when (fixpoint) {
            true -> query(fixpointSolver)
            else -> query(solver)
        }

        val knownDeclarations: List<DeclarationTrackingContext.Declaration>
            get() = context.declarations.toList()

        infix fun BoolExpr.and(other: BoolExpr) = context.mkAnd(this, other)
        infix fun BoolExpr.implies(other: BoolExpr) = context.mkImplies(this, other)
    }

    fun statementIsPossible(state: PredicateState, query: PredicateState): Boolean {
        val ctx = CallCtx(tf)
        val z3State = ctx.convert(state).asAxiom() as BoolExpr
        val z3query = ctx.convert(query).expr as BoolExpr

        val queryPossibility = ctx.build {
            z3State and z3query
        }
        val status = ctx.withSolver {
            add(queryPossibility)
            check()
        }
        return Status.SATISFIABLE == status
    }

    fun mkFixpointStatement(state: PredicateState, positive: PredicateState, negative: PredicateState){
        val ctx = CallCtx(tf)
        val z3State = ctx.convert(state).asAxiom() as BoolExpr
        val z3positive = ctx.convert(positive).expr as BoolExpr
        val z3negative = ctx.convert(negative).expr as BoolExpr
        val allDeclarations = ctx.knownDeclarations
        val argumentDeclarations = allDeclarations.filter { it.name.startsWith("arg$") }
        val argumentsSorts = argumentDeclarations.map { it.sort }.toTypedArray()
        val predicate = ctx.context.mkFuncDecl("function_argument_predicate", argumentsSorts, ctx.context.mkBoolSort())
        val predicateApplication = ctx.build {
            val arguments = argumentDeclarations.map { it.expr }.toTypedArray()
            context.mkApp(predicate, *arguments) as BoolExpr
        }
        val negativePredicateApplication = ctx.build {
            context.mkNot(predicateApplication)
        }
        val positiveStatement = ctx.build {
            (z3State and z3positive) implies predicateApplication
        }
        val negativeStatement = ctx.build {
            (z3State and z3negative) implies negativePredicateApplication
        }
        val declarationExprs = allDeclarations.map { it.expr }.toTypedArray()
        val positiveQuery = ctx.context.mkForall(declarationExprs, positiveStatement, 0, arrayOf(), null, null, null)
        val negativeQuery = ctx.context.mkForall(declarationExprs, negativeStatement, 0, arrayOf(), null, null, null)
        ctx.withSolver(fixpoint = true){
            add(positiveQuery)
            add(negativeQuery)
            val status = check()
            val a = 3
        }
        val a = 3
    }


}

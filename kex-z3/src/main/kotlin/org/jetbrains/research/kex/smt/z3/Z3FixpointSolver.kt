package org.jetbrains.research.kex.smt.z3

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.*
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.term.ArgumentTerm
import org.jetbrains.research.kex.state.transformer.collectArguments
import org.jetbrains.research.kfg.type.TypeFactory
import java.io.File


class Z3FixpointSolver(val tf: TypeFactory) {

    sealed class FixpointResult {
        data class Unknown(val reason: String) : FixpointResult()
        data class Unsat(val core: Array<BoolExpr>) : FixpointResult()
        data class Sat(val result: PredicateState) : FixpointResult()
    }

    class DeclarationTrackingContext : Context() {
        data class Declaration(val name: String, val sort: Sort, val expr: Expr) {
            val isArg: Boolean by lazy { name.startsWith("arg$") }
            val isMemory: Boolean by lazy { name.matches(Regex("__memory__\\d+")) }
        }

        val declarations = hashSetOf<Declaration>()

        override fun mkConst(p0: String?, p1: Sort?) = super.mkConst(p0, p1).apply {
            declarations.add(Declaration("$this", sort, this))
        }

        override fun mkFreshConst(p0: String?, p1: Sort?) = super.mkFreshConst(p0, p1).apply {
            declarations.add(Declaration("$this", sort, this))
        }

    }

    private class DeclarationTrackingExprFactory : Z3ExprFactory() {
        override val ctx = DeclarationTrackingContext()
    }

    private class CallCtx(tf: TypeFactory) {
        val ef = DeclarationTrackingExprFactory()
        val context = ef.ctx
        val z3Context = Z3Context(ef, (1 shl 8) + 1, (1 shl 24) + 1)
        val converter = Z3Converter(tf)

        val options = Z3OptionBuilder()
                .produceUnsatCores(true)
                .fp.engine("spacer")
                .fp.generateProofTrace(true)

                .fp.xform.inlineEager(false)
                .fp.xform.inlineLinear(false)
                .fp.xform.compressUnbound(false)

                .fp.datalog.generateExplanations(true)
                .fp.datalog.similarityCompressor(false)
                .fp.datalog.unboundCompressor(false)
                .fp.datalog.subsumption(false)

                .fp.spacer.iuc.debugProof(true)
                .fp.spacer.q3(false)
                .fp.spacer.simplifyPob(true)


        val solver: Solver
            get() {
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
                return ctx.tryFor(tactic, 10 * 1000).solver
                        ?: throw IllegalStateException("Unable to build solver")
            }

        val fixpointSolver: Solver
            get() = context.mkSolver("HORN")
                    .apply {
                        val params = options.addToParams(context.mkParams())
                        setParameters(params)
                    }
                    ?: throw IllegalStateException("Unable to build solver")

        inline fun <reified T> withSolver(fixpoint: Boolean = false, query: Solver.() -> T) = when (fixpoint) {
            true -> query(fixpointSolver)
            else -> query(solver)
        }

        val knownDeclarations: List<DeclarationTrackingContext.Declaration>
            get() = context.declarations.toList()

        fun convert(ps: PredicateState): Bool_ = converter.convert(ps, ef, z3Context)

        fun build(builder: CallCtx.() -> BoolExpr) = builder()

        infix fun BoolExpr.and(other: BoolExpr) = context.mkAnd(this, other)
        infix fun BoolExpr.implies(other: BoolExpr) = context.mkImplies(this, other)

        operator fun IntExpr.plus(other: IntExpr) = context.mkAdd(this, other) as IntExpr
        operator fun IntExpr.minus(other: IntExpr) = context.mkSub(this, other) as IntExpr
        operator fun IntExpr.rem(other: IntExpr) = context.mkMod(this, other) as IntExpr

        inline fun <reified T : Expr> T.withContext() = translate(context) as T

        fun debugFixpointSmtLib(solver: Solver) = """
                (set-logic HORN)
                ${options.smtLib()}
                
                $solver
                
                (check-sat)
                (get-model)
                (get-info :reason-unknown)

                """.trimIndent()
    }

    private inline fun <reified T : Expr> T.typedSimplify(): T = simplify() as T

    fun argumentVarIdx(state: PredicateState, arguments: List<DeclarationTrackingContext.Declaration>): Map<Int, ArgumentTerm> {
        val (thisArg, otherArgs) = collectArguments(state)
        val indexedArgs = arguments.mapIndexed { index, declaration -> declaration to index }
        return otherArgs.values
                .map { arg ->
                    arg to (indexedArgs.find { it.first.name == arg.name }
                            ?.second
                            ?: throw IllegalStateException("Argument ${arg.name} not found "))
                }
                .map { it.second to it.first }
                .toMap()
    }

    fun memspaceVarIdx(arguments: List<DeclarationTrackingContext.Declaration>): Map<Int, Int> {
        val indexedArgs = arguments.mapIndexed { index, declaration -> declaration to index }
        val memories = indexedArgs.filter { it.first.isMemory }
        val memspaceIdRegEx = Regex("__memory__(\\d+)")
        return memories.map {
            (memspaceIdRegEx.find(it.first.name)?.groupValues?.get(1)?.toInt()
                    ?: throw IllegalStateException("No memspace id")) to it.second
        }.map { it.second to it.first }.toMap()
    }

    fun mkFixpointQuery(state: PredicateState, positive: PredicateState, negative: PredicateState): FixpointResult {
        val ctx = CallCtx(tf)
        val z3State = ctx.convert(state).asAxiom() as BoolExpr
        val z3positive = ctx.convert(positive).expr as BoolExpr
        val z3negative = ctx.convert(negative).expr as BoolExpr
        val allDeclarations = ctx.knownDeclarations
        val argumentDeclarations = allDeclarations.filter { it.isArg || it.isMemory }
        val argumentsSorts = argumentDeclarations.map { it.sort }.toTypedArray()
        val declarationExprs = allDeclarations.map { it.expr }.toTypedArray()

        val predicate = ctx.context.mkFuncDecl("function_argument_predicate", argumentsSorts, ctx.context.mkBoolSort())

        possibilityChecks(z3State, z3positive, z3negative)

        val predicateApplication = ctx.build {
            val arguments = argumentDeclarations.map { it.expr }.toTypedArray()
            context.mkApp(predicate, *arguments) as BoolExpr
        }
        val positiveStatement = ctx.build {
            (z3State and z3positive) implies predicateApplication
        }
        val negativeStatement = ctx.build {
            ((z3State and z3negative) and predicateApplication) implies context.mkFalse()
        }
        val positiveQuery = ctx.context.mkForall(declarationExprs, positiveStatement, 0, arrayOf(), null, null, null).typedSimplify()
        val negativeQuery = ctx.context.mkForall(declarationExprs, negativeStatement, 0, arrayOf(), null, null, null).typedSimplify()

        return ctx.withSolver(fixpoint = true) {
            add(positiveQuery)
            add(negativeQuery)

            File("last_fixpoint_query.smtlib").writeText(ctx.debugFixpointSmtLib(this))

            val status = check()
            when (status) {
                Status.UNKNOWN -> FixpointResult.Unknown(reasonUnknown)
                Status.UNSATISFIABLE -> FixpointResult.Unsat(unsatCore)
                Status.SATISFIABLE -> {
                    val result = convertModel(model, state, argumentDeclarations)
                    FixpointResult.Sat(result)
                }
            }
        }
    }

    private fun convertModel(model: Model, state: PredicateState, argumentDeclarations: List<DeclarationTrackingContext.Declaration>): PredicateState {
        val predicate = model.funcDecls[0]
        val predicateInterpretation = model.getFuncInterp(predicate)
        val argsMapping = argumentVarIdx(state, argumentDeclarations)
        val memspaceMapping = memspaceVarIdx(argumentDeclarations)
        val modelConverter = Z3FixpointModelConverter(argsMapping, memspaceMapping, tf)
        if (predicateInterpretation.numEntries != 0) TODO("Model with entries")
        val elseEntry = predicateInterpretation.`else`
        log.info("$elseEntry")
        return  modelConverter.apply(elseEntry)
    }

    private fun possibilityChecks(state: BoolExpr, positive: BoolExpr, negative: BoolExpr) {
        val ctx = CallCtx(tf)
        fun logQuery(query: String, name: String) {
            val queryName = name.toLowerCase().replace(" ", "_")
            File("check_$queryName.smtlib").writeText(query)
        }

        fun BoolExpr.check(expected: Status, name: String) = ctx.withSolver {
            add(this@check)
            logQuery("$this", name)
            val status = check()
            if (status != expected) {
                throw IllegalArgumentException("$name is not possible")
            }
        }

        ctx.build {
            state.withContext()
        }.check(Status.SATISFIABLE, "State")

        ctx.build {
            state.withContext() and positive.withContext()
        }.check(Status.SATISFIABLE, "Positive path")

        ctx.build {
            state.withContext() and negative.withContext()
        }.check(Status.SATISFIABLE, "Negative path")

        ctx.build {
            state.withContext() and positive.withContext() and negative.withContext()
        }.check(Status.UNSATISFIABLE, "Path exclusiveness")

    }

}

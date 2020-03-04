package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.*
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.term.ArgumentTerm
import org.jetbrains.research.kex.state.transformer.collectArguments
import org.jetbrains.research.kfg.type.TypeFactory
import java.io.File


class Z3FixpointSolver(val tf: TypeFactory) {

    data class QueryCheckStatus(
            val stateNotPossible: Boolean = false,
            val positiveNotPossible: Boolean = false,
            val negativeNotPossible: Boolean = false,
            val exclusivenessNotPossible: Boolean = false
    ) {
        fun raiseIfNotCorrect() {
            if (stateNotPossible || positiveNotPossible || negativeNotPossible || exclusivenessNotPossible)
                throw FixpointQueryException(this)
        }
    }

    class FixpointQueryException(val status: QueryCheckStatus) : Exception() {
        override fun fillInStackTrace(): Throwable = this
    }


    sealed class FixpointResult {
        data class Unknown(val reason: String) : FixpointResult()
        data class Unsat(val core: Array<BoolExpr>) : FixpointResult()
        data class Sat(val result: List<PredicateState>) : FixpointResult()
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
        val z3Context = Z3Context.create(ef)
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

        fun BoolExpr.forall(variables: List<Expr>) = context.mkForall(variables.toTypedArray(), this, 0, arrayOf(), null, null, null)

        fun boolFunction(name: String, argumentsSorts: List<Sort>) = context.mkFuncDecl(name, argumentsSorts.toTypedArray(), context.mkBoolSort())
        fun boolFunctionApp(function: FuncDecl, arguments: List<Expr>) = context.mkApp(function, *arguments.toTypedArray()) as BoolExpr

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

    private fun BoolExpr.typedSimplify(): BoolExpr = simplify() as BoolExpr

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

    private data class Predicate(val idx: Int) {
        fun call(ctx: CallCtx, arguments: List<DeclarationTrackingContext.Declaration>) = ctx.build {
            val argumentsSorts = arguments.map { it.sort }
            val callArguments = arguments.map { it.expr }
            val predicate = boolFunction("function_argument_predicate_$idx", argumentsSorts)
            boolFunctionApp(predicate, callArguments)
        }
        companion object{
            fun getPredicateIdx(name: String): Int {
                val idxRegex = Regex("function_argument_predicate_(\\d+)")
                return idxRegex.find(name)?.groupValues?.get(1)?.toInt()
                        ?: throw IllegalStateException("No predicate idx")
            }
        }
    }

    fun mkFixpointQuery(state: PredicateState, positivePaths: List<PredicateState>, query: PredicateState): FixpointResult {
        val ctx = CallCtx(tf)
        val z3State = ctx.convert(state).asAxiom() as BoolExpr
        val z3positive = positivePaths.map { ctx.convert(it).expr as BoolExpr }
        val z3query = ctx.convert(query).expr as BoolExpr
        val allDeclarations = ctx.knownDeclarations
        val argumentDeclarations = allDeclarations.filter { it.isArg || it.isMemory }
        val declarationExprs = allDeclarations.map { it.expr }

        possibilityChecks(z3State, z3positive, z3query)

        val predicates = z3positive.indices.map { idx -> Predicate(idx)}
        val predicateApplications = predicates.map { it.call(ctx, argumentDeclarations) }
        val positiveStatements = z3positive.mapIndexed { idx, it ->
            ctx.build {
                val statement = (z3State and it) implies predicateApplications[idx]
                statement.forall(declarationExprs)
            }
        }
        val queryStatement = ctx.build {
            val applications = predicateApplications.toTypedArray()
            val allApplications = context.mkOr(*applications)
            val statement = ((z3State and z3query) and allApplications) implies context.mkFalse()
            statement.forall(declarationExprs)
        }

        return ctx.withSolver(fixpoint = true) {
            for (statement in positiveStatements) {
                add(statement)
            }
            add(queryStatement)

            File("last_fixpoint_query.smtlib").writeText(ctx.debugFixpointSmtLib(this))

            val status = check()
            when (status) {
                Status.UNKNOWN -> FixpointResult.Unknown(reasonUnknown)
                Status.UNSATISFIABLE -> FixpointResult.Unsat(unsatCore)
                Status.SATISFIABLE -> {
                    val result = convertModel(model, state, predicates, argumentDeclarations)
                    FixpointResult.Sat(result)
                }
            }
        }
    }

    private fun convertModel(
            model: Model,
            state: PredicateState,
            predicates: List<Predicate>,
            argumentDeclarations: List<DeclarationTrackingContext.Declaration>
    ): List<PredicateState> {
        val modelPredicates = model.funcDecls.map { Predicate.getPredicateIdx("${it.name}") to it }.toMap()
        return predicates.map {
            val predicate = modelPredicates[it.idx] ?: return@map falseState()
            val predicateInterpretation = model.getFuncInterp(predicate)
            val argsMapping = argumentVarIdx(state, argumentDeclarations)
            val memspaceMapping = memspaceVarIdx(argumentDeclarations)
            val modelConverter = Z3FixpointModelConverter(argsMapping, memspaceMapping, tf)
            if (predicateInterpretation.numEntries != 0) TODO("Model with entries")
            val elseEntry = predicateInterpretation.`else`
            modelConverter.apply(elseEntry)
        }
    }

    private fun possibilityChecks(state: BoolExpr, positives: List<BoolExpr>, query: BoolExpr) {
        val correctness = QueryCheckStatus()
        val ctx = CallCtx(tf)
        fun logQuery(query: String, name: String) {
            val queryName = name.toLowerCase().replace(" ", "_")
            File("check_$queryName.smtlib").writeText(query)
        }

        fun BoolExpr.check(expected: Status, name: String) = ctx.withSolver {
            add(this@check)
            logQuery("$this", name)
            val status = check()
            status == expected
        }

        correctness.copy(stateNotPossible = ctx.build {
            state.withContext()
        }.check(Status.SATISFIABLE, "State"))
        correctness.copy(negativeNotPossible = ctx.build {
            state.withContext() and query.withContext()
        }.check(Status.SATISFIABLE, "Query path"))
        for (positive in positives) {
            correctness.copy(positiveNotPossible = ctx.build {
                state.withContext() and positive.withContext()
            }.check(Status.SATISFIABLE, "Positive path"))
            correctness.copy(exclusivenessNotPossible = ctx.build {
                state.withContext() and positive.withContext() and query.withContext()
            }.check(Status.UNSATISFIABLE, "Path exclusiveness"))
        }
        correctness.raiseIfNotCorrect()
    }

}

package org.jetbrains.research.kex.smt.z3

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.*
import org.jetbrains.research.kex.smt.z3.expr.Optimizer
import org.jetbrains.research.kex.smt.z3.fixpoint.*
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.FieldLoadTerm
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.type.TypeFactory
import java.io.File
import kotlin.time.ExperimentalTime
import kotlin.time.measureTimedValue

class Z3FixpointSolver(val tf: TypeFactory) {

    private class CallCtx(tf: TypeFactory, callConverter: CallPredicateConverter? = null) : AutoCloseable {
        val declarationTracker = DeclarationTracker()
        val ef = when {
            callConverter != null -> FixpointExprFactory.withDeclarationsTrackingAndCallConverter(declarationTracker, callConverter)
            else -> FixpointExprFactory.withDeclarationsTracking(declarationTracker)
        }
        val context = ef.ctx
        val z3Context = Z3Context.create(ef)
        val converter = Z3Converter(tf)

        val options = Z3OptionBuilder()
                .timeout(100 * 1000)
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

        val fixpointSolver: Solver
            get() = context.mkSolver("HORN")
                    .apply {
                        val params = options.addToParams(context.mkParams())
                        setParameters(params)
                    }
                    ?: throw IllegalStateException("Unable to build solver")

        @OptIn(ExperimentalTime::class)
        inline fun <reified T> withSolver(query: Solver.() -> T): T {
            val result = measureTimedValue {
                query(fixpointSolver)
            }
            log.info("Run solver for ${result.duration}")
            return result.value
        }

        val knownDeclarations: List<DeclarationTracker.Declaration>
            get() = declarationTracker.declarations.toList()

        fun convert(ps: PredicateState): Bool_ = converter.convert(ps, ef, z3Context)

        fun build(builder: CallCtx.() -> BoolExpr) = builder()

        infix fun BoolExpr.and(other: BoolExpr) = context.mkAnd(this, other)
        infix fun BoolExpr.or(other: BoolExpr) = context.mkOr(this, other)
        infix fun BoolExpr.implies(other: BoolExpr) = context.mkImplies(this, other)
        fun BoolExpr.not() = context.mkNot(this)
        fun BoolExpr.forall(variables: List<Expr>): Quantifier = when {
            variables.isEmpty() -> {
                val dummy = context.mkFreshConst("dummy", context.mkBoolSort())
                context.mkForall(arrayOf(dummy), this, 0, arrayOf(), null, null, null)
            }
            else -> context.mkForall(variables.toTypedArray(), this, 0, arrayOf(), null, null, null)
        }

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

        override fun close() = context.close()
    }

    private fun BoolExpr.optimize(ctx: CallCtx): BoolExpr = Optimizer(ctx.context).apply(typedSimplify())

    private fun BoolExpr.typedSimplify(): BoolExpr = simplify() as BoolExpr

    private data class Predicate(val idx: Int) {
        val name = "$BASE_NAME$idx"
        fun call(ctx: CallCtx, arguments: List<DeclarationTracker.Declaration>) = ctx.build {
            val argumentsSorts = arguments.map { it.sort }
            val callArguments = arguments.map { it.expr }
            val predicate = boolFunction(name, argumentsSorts)
            boolFunctionApp(predicate, callArguments)
        }

        companion object {
            const val BASE_NAME = "function_argument_predicate__"
            val idxRegex = Regex("$BASE_NAME(\\d+)")
            fun getPredicateIdx(name: String): Int {
                return idxRegex.find(name)?.groupValues?.get(1)?.toInt()
                        ?: throw IllegalStateException("No predicate idx")
            }
        }
    }

    fun analyzeRecursion(
            state: PredicateState,
            recursiveCalls: Map<CallPredicate, Map<Field, FieldLoadTerm>>,
            rootCall: CallPredicate,
            recursionPath: PredicateState,
            positive: PredicateState,
            query: PredicateState
    ): FixpointResult {
        val recursionPredicate = Predicate(0)
        val recursionConverter = CallPredicateConverterWithRecursion(recursiveCalls, rootCall, recursionPredicate.name)
        val unknownCallsProcessor = UnknownCallsProcessor(ignore = recursiveCalls.keys, replaceWithArray = false) + state + recursionPath + positive + query
        if (unknownCallsProcessor.hasUnknownCalls()) throw IllegalArgumentException("Recursive with unknowns")
        return CallCtx(tf, recursionConverter).use { ctx ->
            val rootPredicate = recursionConverter.buildPredicate(rootCall, ctx.ef, ctx.z3Context, ctx.converter).expr as BoolExpr

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

            val recursionStmt = ctx.build {
                val statement = (z3State and z3Positive) implies rootPredicate
                statement.forall(declarationExprs)
            }.optimize(ctx)

            val queryStmt = ctx.build {
                val statement = (z3State and z3Query and rootPredicate) implies context.mkFalse()
                statement.forall(declarationExprs)
            }.optimize(ctx)

            log.debug("State:\n$z3State\nRecursion:\n$z3Recursion\nPositive:\n$z3Positive\nQuery:\n$z3Query")
            log.debug("Recursion:\n$recursionStmt\nQuery:\n$queryStmt")

            ctx.callSolver(listOf(recursionPredicate), recursionConverter.mapper, listOf(recursionStmt), queryStmt)
        }
    }

     fun mkFixpointQueryV2(state: PredicateState, positivePaths: List<PredicateState>, query: PredicateState): FixpointResult {
         val callPredicateConverter = CallPredicateConverterWithMemory()
         return CallCtx(tf, callPredicateConverter).use { ctx ->
             val z3State = ctx.build {
                 convert(state).asAxiom() as BoolExpr
             }
             val z3positive = positivePaths.map { ctx.convert(it).asAxiom() as BoolExpr }
             val z3query = ctx.convert(query).asAxiom() as BoolExpr

             log.debug("State:\n$z3State\nPositive:\n$z3positive\nQuery:\n$z3query")

             val declarationExprs = ctx.knownDeclarations.map { it.expr }
             val argumentDeclarations = ctx.knownDeclarations.filter { it.isValuable() }
             val declarationMapping = ModelDeclarationMapping.create(argumentDeclarations, state, query, *positivePaths.toTypedArray())

             log.debug("$argumentDeclarations")

             val predicates = z3positive.indices.map { idx -> Predicate(idx) }
             val predicateApplications = predicates.map { it.call(ctx, argumentDeclarations) }
             val positiveStatements = z3positive.mapIndexed { idx, it ->
                 ctx.build {
                     val statement = (z3State and it) implies predicateApplications[idx]
                     statement.forall(declarationExprs).typedSimplify()
                 }
             }
             val queryStatement = ctx.build {
                 val applications = predicateApplications.toTypedArray()
                 val allApplications = context.mkOr(*applications)
                 val statement = ((z3State and z3query) and allApplications) implies context.mkFalse()
                 statement.forall(declarationExprs).typedSimplify()
             }
             ctx.callSolver(predicates, declarationMapping, positiveStatements, queryStatement)
         }
     }

    fun mkFixpointQuery(state: PredicateState, positivePaths: List<PredicateState>, query: PredicateState): FixpointResult =
            CallCtx(tf).use { ctx ->
                val unknownCallsProcessor = UnknownCallsProcessor() + state + positivePaths + query
                val state = unknownCallsProcessor.apply(state)
                val positivePaths = unknownCallsProcessor.apply(positivePaths)
                val query = unknownCallsProcessor.apply(query)

                val z3State = ctx.build {
                    convert(state).asAxiom() as BoolExpr
                }
                val z3positive = positivePaths.map { ctx.convert(it).asAxiom() as BoolExpr }
                val z3query = ctx.convert(query).asAxiom() as BoolExpr

                log.debug("State:\n$z3State\nPositive:\n$z3positive\nQuery:\n$z3query")

                val declarationExprs = ctx.knownDeclarations.map { it.expr }
                val argumentDeclarations = ctx.knownDeclarations.filter { it.isValuable() }
                val declarationMapping = ModelDeclarationMapping.create(argumentDeclarations, state, query, *positivePaths.toTypedArray())
                unknownCallsProcessor.addToDeclarationMapping(declarationMapping)

                val predicates = z3positive.indices.map { idx -> Predicate(idx) }
                val predicateApplications = predicates.map { it.call(ctx, argumentDeclarations) }
                val positiveStatements = z3positive.mapIndexed { idx, it ->
                    ctx.build {
                        val statement = (z3State and it) implies predicateApplications[idx]
                        statement.forall(declarationExprs).typedSimplify()
                    }
                }
                val queryStatement = ctx.build {
                    val applications = predicateApplications.toTypedArray()
                    val allApplications = context.mkOr(*applications)
                    val statement = ((z3State and z3query) and allApplications) implies context.mkFalse()
                    statement.forall(declarationExprs).typedSimplify()
                }
                ctx.callSolver(predicates, declarationMapping, positiveStatements, queryStatement)
            }

    private fun CallCtx.callSolver(
            predicates: List<Predicate>,
            mapper: ModelDeclarationMapping,
            positives: List<BoolExpr>,
            query: BoolExpr
    ) = withSolver {
        for (statement in positives) {
            add(statement)
        }
        add(query)

        log.debug(debugFixpointSmtLib(this))
        File("last_fixpoint_query.smtlib").writeText(debugFixpointSmtLib(this))

        val status = check()
        when (status) {
            Status.UNKNOWN -> FixpointResult.Unknown(reasonUnknown)
            Status.UNSATISFIABLE -> FixpointResult.Unsat(unsatCore)
            Status.SATISFIABLE -> {
                val result = convertModel(model, mapper, predicates)
                FixpointResult.Sat(result)
            }
        }
    }

    private fun CallCtx.convertModel(
            model: Model,
            mapping: ModelDeclarationMapping,
            predicates: List<Predicate>
    ): List<PredicateState> {
        val modelPredicates = model.funcDecls.map { Predicate.getPredicateIdx("${it.name}") to it }.toMap()
        return predicates.map {
            val predicate = modelPredicates[it.idx] ?: return@map falseState()
            val predicateInterpretation = model.getFuncInterp(predicate)
            val modelConverter = FixpointModelConverter(mapping, tf, z3Context)
            if (predicateInterpretation.numEntries != 0) TODO("Model with entries")
            val elseEntry = predicateInterpretation.`else`
            log.debug("\n$elseEntry")
            log.debug("\n${mapping.declarations}")
            log.debug("\n${z3Context.getTypeMapping()}")
            modelConverter.apply(elseEntry)
        }
    }

}

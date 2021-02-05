package org.jetbrains.research.kex.smt.z3.fixpoint

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.*
import org.jetbrains.research.kex.smt.z3.Bool_
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.smt.z3.Z3EngineContext
import org.jetbrains.research.kex.smt.z3.Z3OptionBuilder
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.FixpointExprFactory
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.Declaration
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.DeclarationTracker
import org.jetbrains.research.kex.smt.z3.fixpoint.model.FixpointModelConverter
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.query.FixpointSolverQuery
import org.jetbrains.research.kex.smt.z3.fixpoint.query.StatementBuilder
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kfg.type.TypeFactory
import java.io.File
import kotlin.time.ExperimentalTime
import kotlin.time.measureTimedValue

open class FixpointCallCtx(
    val tf: TypeFactory,
    val solverQuery: FixpointSolverQuery
) : AutoCloseable {
    val declarationTracker = DeclarationTracker()
    val converter = solverQuery.makeConverter(tf)

    val context: Z3EngineContext
        get() = ef.ctx

    val ef by lazy { mkExprFactory() }
    val z3Context by lazy { mkContext() }
    val options by lazy { mkOptions() }
    val fixpointSolver by lazy { mkSolver() }

    open fun mkContext() = Z3Context.createInitialized(
        ef, *solverQuery.allStatesForMemoryInitialization().toTypedArray()
    )

    open fun mkExprFactory() =
        FixpointExprFactory.builder()
            .normal()
            .withDeclarationsTracking(declarationTracker)
            .build()

    open fun mkSolver(): Solver =
        ef.ctx.mkSolver("HORN").apply {
            val params = options.addToParams(ef.ctx.mkParams())
            setParameters(params)
        } ?: error("Unable to build solver")

    open fun mkOptions() = Z3OptionBuilder()
        .timeout(100 * 1000)
        .produceUnsatCores(true)
        .fp.engine("spacer")
        .fp.xform.inlineEager(false)
        .fp.xform.inlineLinear(false)
        .fp.spacer.simplifyPob(true)

    @OptIn(ExperimentalTime::class)
    inline fun <reified T> withSolver(query: Solver.() -> T): T {
        val result = measureTimedValue {
            query(fixpointSolver)
        }
        log.info("Run solver for ${result.duration}")
        return result.value
    }

    val knownDeclarations: List<Declaration>
        get() = declarationTracker.declarations.toList()

    fun convert(ps: PredicateState): Bool_ = converter.convertWithMemoryReset(ps, ef, z3Context)

    fun build(builder: FixpointCallCtx.() -> BoolExpr) = builder()

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

    fun boolFunction(name: String, argumentsSorts: List<Sort>) =
        context.mkFuncDecl(name, argumentsSorts.toTypedArray(), context.mkBoolSort())

    fun boolFunctionApp(function: FuncDecl, arguments: List<Expr>) =
        context.mkApp(function, *arguments.toTypedArray()) as BoolExpr

    operator fun IntExpr.plus(other: IntExpr) = context.mkAdd(this, other) as IntExpr
    operator fun IntExpr.minus(other: IntExpr) = context.mkSub(this, other) as IntExpr
    operator fun IntExpr.rem(other: IntExpr) = context.mkMod(this, other) as IntExpr

    fun BoolExpr.typedSimplify(): BoolExpr = simplify() as BoolExpr

    override fun close() = context.close()

    internal fun callSolver(
        predicates: List<Z3FixpointSolver.Predicate>,
        mapper: ModelDeclarationMapping,
        statementBuilder: StatementBuilder
    ) = withSolver {
        statementBuilder.normal().makeAsserts(this)

        File("last_fixpoint_query.smtlib").writeText(debugFixpointSmtLib(statementBuilder))

        val status = check()
        when (status) {
            Status.SATISFIABLE -> {
                val result = convertModel(model, mapper, predicates)
                FixpointResult.Sat(result)
            }
            Status.UNKNOWN -> FixpointResult.Unknown(reasonUnknown)
            Status.UNSATISFIABLE -> FixpointResult.Unsat(unsatCore)
        }
    }

    private fun convertModel(
        model: Model,
        mapping: ModelDeclarationMapping,
        predicates: List<Z3FixpointSolver.Predicate>
    ): List<RecoveredModel> {
        val modelPredicates =
            model.funcDecls.map { Z3FixpointSolver.Predicate.getPredicateIdx("${it.name}") to it }.toMap()
        return predicates.map {
            val predicate = modelPredicates[it.idx] ?: return@map RecoveredModel.error()
            val predicateInterpretation = model.getFuncInterp(predicate)
            val modelConverter = FixpointModelConverter(mapping, tf, z3Context)
            if (predicateInterpretation.numEntries != 0) TODO("Model with entries")
            val elseEntry = predicateInterpretation.`else`
            log.debug("\n$elseEntry")
            log.debug("\n${mapping}")
            log.debug("\n${z3Context.getTypeMapping()}")
            modelConverter.apply(elseEntry)
        }
    }

    private fun debugFixpointSmtLib(statementBuilder: StatementBuilder) = """
            (set-logic HORN)
            ${options.smtLib()}
            
            ${statementBuilder.debug().debugSmtLib()}
            
            (check-sat)
            (get-model)
            (get-info :reason-unknown)

            """.trimIndent()

}
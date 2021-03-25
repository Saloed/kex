package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.*
import com.microsoft.z3.enumerations.Z3_ast_kind
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readText


@ExperimentalPathApi
fun main(args: Array<String>) {
    val options = Options()
        .addOption(Option("f", "file", true, "Z3 asserts").apply { isRequired = true })

    val parsedArgs = DefaultParser().parse(options, args)
    val file = parsedArgs.getOptionValue("file").let { Paths.get(it) }
    val smtlib2Source = file.readText()
    val ctx = Context()
    val asserts = ctx.parseSMTLIB2String(smtlib2Source, emptyArray(), emptyArray(), emptyArray(), emptyArray())
    check(asserts.size >= 2) { "Unexpected asserts" }
    val firstFormula = asserts[0]
    val secondFormula = asserts[1]
    val additionalConstraints = asserts.drop(2)

    val bindings = findVariableBindings(firstFormula, secondFormula, additionalConstraints, ctx)
    return
    if (!validateBindings(firstFormula, secondFormula, bindings, ctx)) {
        error("Incorrect bindings")
    }
    val formulaWithBindings = printBindings(firstFormula, secondFormula, bindings, ctx)
    println(formulaWithBindings)
}

fun printBindings(first: BoolExpr, second: BoolExpr, bindings: Map<Expr, Expr>, ctx: Context): String {
    val solver = ctx.mkSolver()
    solver.add(first)
    solver.add(second)
    for ((key, value) in bindings.entries.sortedBy { "${it.key}" }) {
        solver.add(ctx.mkEq(key, value))
    }
    return solver.toString()
}

fun validateBindings(
    first: BoolExpr,
    second: BoolExpr,
    bindings: Map<Expr, Expr>,
    ctx: Context
): Boolean {
    val bindingStatements = bindings.map { ctx.mkEq(it.key, it.value) }
    val statement = ctx.mkImplies(
        ctx.mkAnd(*bindingStatements.toTypedArray()),
        ctx.mkEq(first, second)
    )
    val variables = collectVariables(first) + collectVariables(second) + bindings.keys
    val query = ctx.mkForall(variables.toTypedArray(), statement, 0, arrayOf(), null, null, null)
    val solver = ctx.mkSolver()
    solver.add(query)
    val status = solver.check()
    println("Validation: $status")
    return status == Status.SATISFIABLE
}

private fun findVariableBindings(
    first: BoolExpr,
    second: BoolExpr,
    other: List<BoolExpr>,
    ctx: Context
): Map<Expr, Expr> {
    val bindingSources = listOf(
        createBinding(ctx, collectVariables(first).toList()),
        createBinding(ctx, collectVariables(second).toList())
    ).associateBy { it.tag }
    val orderedVariables = (other + listOf(first, second)).map { collectVariables(it) }.flatten().toSet().toList()

    val bindingVars = mutableMapOf<Expr, IntExpr>()
    val bindings = mutableListOf<BoolExpr>()
    val constraints = mutableListOf<BoolExpr>()

    for (variable in orderedVariables) {
        if (variable.tag() != VarTag.GOOD) continue
        val bindingVar = ctx.mkFreshConst("var_binding", ctx.mkIntSort()) as IntExpr
        val bindingSource = bindingSources.getValue(variable.tag().opposite())
        val bindingCandidates = bindingSource.bindingArray(variable)
        bindingVars += variable to bindingVar
        constraints += bindingCandidates.indices.map { ctx.mkEq(bindingVar, ctx.mkInt(it)) }
            .let { ctx.mkOr(*it.toTypedArray()) }

        val bindingValue = bindingCandidates.withIndex().reduce { (_, acc), (i, candidate) ->
            IndexedValue(i, ctx.mkITE(ctx.mkEq(bindingVar, ctx.mkInt(i)), candidate, acc))
        }
        bindings += ctx.mkEq(variable, bindingValue.value)
    }

    val allBindings = ctx.mkAnd(*bindings.toTypedArray(), *other.toTypedArray())
    val allConstraints = ctx.mkAnd(*constraints.toTypedArray())

    val solver = ctx.mkSolver("HORN")
    val params = ctx.mkParams()
    Z3OptionBuilder()
        .fp.engine("spacer")
        .fp.xform.inlineLinear(false)
        .fp.xform.inlineEager(false)
        .produceUnsatCores(true)
        .addToParams(params)
    solver.setParameters(params)
    val bindVariables = bindingVars.values.toList()
    val bindVarPredicate = ctx.mkApp(
        ctx.mkFuncDecl(
            "var_binding_predicate",
            bindVariables.map { it.sort }.toTypedArray(),
            ctx.mkBoolSort()
        ), *bindVariables.toTypedArray()
    ) as BoolExpr
    val specialPredicate = ctx.mkApp(
        ctx.mkFuncDecl(
            "special_predicate",
            orderedVariables.map { it.sort }.toTypedArray(),
            ctx.mkBoolSort()
        ), *orderedVariables.toTypedArray()
    ) as BoolExpr

    solver.add(
        ctx.mkForall(
            ctx.mkImplies(
                ctx.mkImplies(ctx.mkAnd(allConstraints, allBindings), ctx.mkEq(first, second)),
                bindVarPredicate
            ),
            orderedVariables + bindVariables
        )
    )

    solver.add(
        ctx.mkForall(
            ctx.mkImplies(
                ctx.mkAnd(
                    bindVarPredicate,
                    ctx.mkImplies(ctx.mkAnd(allConstraints, allBindings), ctx.mkNot(ctx.mkEq(first, second))),
                ),
                ctx.mkFalse()
            ),
            orderedVariables + bindVariables
        )
    )

    println(solver)

    println(solver.check())
    println(solver.unsatCore.contentToString())
    println(solver.reasonUnknown)

    val model = solver.model
    println(model)
    val actualBinding = mutableMapOf<Expr, Expr>()
    for ((variable, bindingVar) in bindingVars) {
        val modelValue = model.evaluate(bindingVar, false) as IntNum
        val source = bindingSources.getValue(variable.tag().opposite()).bindingArray(variable)
        actualBinding += variable to source[modelValue.int]
    }

    println(actualBinding)

    return actualBinding
}

fun Context.mkForall(body: Expr, variables: List<Expr>) =
    mkForall(variables.toTypedArray(), body, 0, arrayOf(), null, null, null)

private fun createBinding(ctx: Context, variables: List<Expr>): Bindings {
    if (variables.isEmpty()) error("No variables")
    val tag = variables.first().tag()
    val bools = variables.filter { it.type() == VarType.BOOL }
    val ints = variables.filter { it.type() == VarType.INT }
    val arrays = variables.filter { it.type() == VarType.INT_ARRAY }
    return Bindings(tag, arrays, ints, bools)
}

enum class VarTag {
    BAD, GOOD;

    fun opposite() = when (this) {
        BAD -> GOOD
        GOOD -> BAD
    }
}

enum class VarType {
    BOOL, INT, INT_ARRAY
}

data class Bindings(
    val tag: VarTag,
    val arrays: List<Expr>,
    val ints: List<Expr>,
    val bools: List<Expr>
) {
    fun bindingArray(variable: Expr): List<Expr> {
        check(variable.tag() != tag) { "Try to select from same tag" }
        val type = variable.type()
        return when (type) {
            VarType.BOOL -> bools
            VarType.INT -> ints
            VarType.INT_ARRAY -> arrays
        }
    }
}

private fun Expr.tag(): VarTag {
    val text = "$this"
    if (text.startsWith("bad") || text.startsWith("|bad")) return VarTag.BAD
    if (text.startsWith("good") || text.startsWith("|good")) return VarTag.GOOD
    error("Unexpected var name: $text")
}

private fun Expr.type(): VarType = when {
    isBool -> VarType.BOOL
    isInt -> VarType.INT
    isArray -> VarType.INT_ARRAY
    else -> error("Unexpected variable sort: $this")
}

fun possibleVariableAssignments(ctx: Context, variables: Set<Expr>): BoolExpr {
    val assignments = variables.map { it to possibleVariableAssignments(it, variables - it) }
    val variants = assignments.map { (variable, candidates) -> candidates.map { ctx.mkEq(variable, it) } }
        .map { ctx.mkOr(*it.toTypedArray()) }
    return ctx.mkAnd(*variants.toTypedArray())
}

fun possibleVariableAssignments(variable: Expr, variables: Set<Expr>): List<Expr> =
    variables.filter { it.sort == variable.sort }


fun normalizeModel(ctx: Context, expr: Expr, variables: List<Expr>): Expr {
    when (expr.astKind) {
        Z3_ast_kind.Z3_VAR_AST -> {
            return variables[expr.index]
        }
        Z3_ast_kind.Z3_APP_AST -> {
            if (expr.numArgs == 0) return expr
            val newArgs = expr.args.map { normalizeModel(ctx, it, variables) }
            return ctx.mkApp(expr.funcDecl, *newArgs.toTypedArray())
        }
        else -> return expr
    }
}

fun collectVariables(expr: Expr, variables: MutableSet<Expr> = mutableSetOf()): Set<Expr> {
    when (expr.astKind) {
        Z3_ast_kind.Z3_VAR_AST -> {
            variables.add(expr)
        }
        Z3_ast_kind.Z3_APP_AST -> {
            if (expr.isConst && !expr.isTrue && !expr.isFalse) {
                variables.add(expr)
            } else {
                expr.args.forEach { collectVariables(it, variables) }
            }
        }
        else -> {
        }
    }
    return variables
}


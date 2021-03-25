package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
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
    val z3Context = Context()
    val asserts = z3Context.parseSMTLIB2String(smtlib2Source, emptyArray(), emptyArray(), emptyArray(), emptyArray())
    val variables = mutableSetOf<Expr>()
    asserts.forEach { collectVariables(it, variables) }
    val orderedVariables = variables.toList()
    val variableSorts = orderedVariables.map { it.sort }
    val predicate = z3Context.mkFuncDecl(
        "variable_mapping_predicate", variableSorts.toTypedArray(), z3Context.mkBoolSort()
    )
    check(asserts.size >= 2) { "Unexpected asserts" }
    val variableAssignments = possibleVariableAssignments(z3Context, variables)
    val specialConditions = asserts.drop(2).toTypedArray()
    val positiveStatement = z3Context.mkImplies(
        z3Context.mkAnd(
            z3Context.mkEq(asserts[0], asserts[1]),
            variableAssignments,
            *specialConditions
        ),
        z3Context.mkApp(predicate, *orderedVariables.toTypedArray()) as BoolExpr
    )
    val negativeStatement = z3Context.mkImplies(
        z3Context.mkAnd(
            z3Context.mkNot(z3Context.mkEq(asserts[0], asserts[1])),
            variableAssignments,
            *specialConditions,
            z3Context.mkApp(predicate, *orderedVariables.toTypedArray()) as BoolExpr
        ), z3Context.mkFalse()
    )

    val positiveQuery =
        z3Context.mkForall(orderedVariables.toTypedArray(), positiveStatement, 0, arrayOf(), null, null, null)
    val negativeQuery =
        z3Context.mkForall(orderedVariables.toTypedArray(), negativeStatement, 0, arrayOf(), null, null, null)

    val solver = z3Context.mkSolver("HORN")
    val params = z3Context.mkParams()
    val solverOptions = Z3OptionBuilder()
        .fp.engine("spacer")
        .fp.xform.inlineEager(false)
        .fp.xform.inlineLinear(false)
        .fp.spacer.simplifyPob(true)
    solverOptions.addToParams(params)
    solver.setParameters(params)

    solver.add(positiveQuery)
    solver.add(negativeQuery)
    println(solver)

    println(solver.check())

    val model = normalizeModel(z3Context, solver.model.getFuncInterp(predicate).`else`, orderedVariables)
    val simplifyParams = z3Context.mkParams()
    val simplifiedModel = model.simplify(simplifyParams)
    println(simplifiedModel)
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

fun collectVariables(expr: Expr, variables: MutableSet<Expr>) {
    when (expr.astKind) {
        Z3_ast_kind.Z3_VAR_AST -> {
            variables.add(expr)
        }
        Z3_ast_kind.Z3_APP_AST -> {
            if (expr.isConst && !expr.isTrue && !expr.isFalse) {
                variables.add(expr)
                return
            }
            expr.args.forEach { collectVariables(it, variables) }
        }
        else -> return
    }
}


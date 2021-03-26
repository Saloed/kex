package org.jetbrains.research.kex.smt.z3.utilities

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.enumerations.Z3_ast_kind
import java.nio.file.Path
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.Path

@OptIn(ExperimentalPathApi::class)
fun Path.parent() = parent ?: Path(".")

fun Context.printAsserts(asserts: List<BoolExpr>): String{
    val solver = mkSolver()
    asserts.forEach { solver.add(it) }
    return solver.toString()
}

fun Expr.name() = "${this.funcDecl.name}"

fun Context.mkForall(body: Expr, variables: List<Expr>) =
    mkForall(variables.toTypedArray(), body, 0, arrayOf(), null, null, null)

fun collectVariables(expr: Expr) = countVariables(expr).keys

fun countVariables(expr: Expr): Map<Expr, Int> {
    val variables = mutableMapOf<Expr, Int>()
    countVariables(expr, variables)
    return variables
}

private fun countVariables(expr: Expr, variables: MutableMap<Expr, Int>) {
    when (expr.astKind) {
        Z3_ast_kind.Z3_VAR_AST -> {
            variables[expr] = (variables[expr] ?: 0) + 1
        }
        Z3_ast_kind.Z3_APP_AST -> {
            if (expr.isConst && !expr.isTrue && !expr.isFalse) {
                variables[expr] = (variables[expr] ?: 0) + 1
            } else {
                expr.args.forEach { countVariables(it, variables) }
            }
        }
        else -> {
        }
    }
}

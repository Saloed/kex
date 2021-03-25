package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.Z3Exception
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readText
import kotlin.io.path.writeText


@ExperimentalPathApi
fun main(args: Array<String>) {
    val options = Options()
        .addOption(Option("f", "file", true, "Z3 asserts").apply { isRequired = true })

    val parsedArgs = DefaultParser().parse(options, args)
    val file = parsedArgs.getOptionValue("file").let { Paths.get(it) }
    val smtlib2Source = file.readText()
    val searchContext = SearchContext(smtlib2Source)
    searchContext.loop()
    val result = searchContext.smtlibWithDeclarations()
    file.writeText(result)
}

val missingVariableRe = Regex("\\(error \"line \\d+ column \\d+: unknown constant (.*)\"\\)")
val arrayExpectedRe =
    Regex("\\(error \"line (\\d+) column (\\d+): store expects the first argument sort to be an array\"\\)")
val intExpectedRe =
    Regex("\\(error \"line (\\d+) column (\\d+): Sort mismatch at argument #(\\d+) for function \\(declare-fun (.*) \\(Int Int\\) \\w+\\) supplied sort is Bool\"\\)")
val incompatibleSortsRe = Regex("\\(error \"line (\\d+) column (\\d+): Sorts Bool and (.*) are incompatible\"\\)")
val incompatibleSorts2Re = Regex("\\(error \"line (\\d+) column (\\d+): Sorts (.*) and Bool are incompatible\"\\)")

const val VAR_NAME_PATTERN = "[A-Za-z\\d#!_\\-\\+\\|]+"

data class Var(val name: String, var type: String = "Bool") {
    fun symbol(ctx: Context) = ctx.mkSymbol(name)
    fun sort(ctx: Context) = when (type) {
        "Bool" -> ctx.mkBoolSort()
        "Int" -> ctx.mkIntSort()
        "(Array Int Int)" -> ctx.mkArraySort(ctx.mkIntSort(), ctx.mkIntSort())
        else -> error("Unexpected type: $type")
    }

    fun funDecl(ctx: Context): FuncDecl = ctx.mkFuncDecl(symbol(ctx), emptyArray(), sort(ctx))

}

class SearchContext(val smtlib2Source: String) {
    val z3Context = Context(mapOf("enable_function_call_support" to "true"))
    val vars = mutableMapOf<String, Var>()

    fun loop() {
        while (true) {
            try {
                parse()
                return
            } catch (ex: Z3Exception) {
                val message = ex.message?.lines()?.filter { it.isNotBlank() } ?: emptyList()
                message.forEach { analyzeMessage(it, smtlib2Source) }
            }
        }
    }

    private fun parse(): Array<out BoolExpr> {
        val variables = vars.values.toList()
        val symbols = variables.map { it.symbol(z3Context) }.toTypedArray()
        val decls = variables.map { it.funDecl(z3Context) }.toTypedArray()
        return z3Context.parseSMTLIB2String(
            smtlib2Source,
            emptyArray(),
            emptyArray(),
            symbols,
            decls
        )
    }

    fun smtlibWithDeclarations(): String {
        val asserts = parse()
        val solver = z3Context.mkSolver()
        for (assert in asserts) {
            solver.add(assert)
        }
        return solver.toString()
    }

    fun variable(varName: String): Var {
        check(varName.isNotBlank()) { "No name" }
        return vars.getOrPut(varName) { Var(varName) }
    }

    fun analyzeMessage(statement: String, smtlib2Statement: String) {
        println(statement)
        val missingVar = missingVariableRe.find(statement)
        if (missingVar != null) {
            variable(missingVar.groupValues[1])
            return
        }
        val arrayExpected = arrayExpectedRe.find(statement)
        if (arrayExpected != null) {
            val (line, column) = arrayExpected.destructured
            val linesTrimmed = trimStatement(smtlib2Statement, line.toInt(), column.toInt())
            val storePattern = Regex("\\(store\\s+($VAR_NAME_PATTERN)\\s+$VAR_NAME_PATTERN\\s+$VAR_NAME_PATTERN\\)")
            val storePredicate = storePattern.find(linesTrimmed)
                ?: error("No store predicate found")
            val varName = storePredicate.groupValues[1]
            val variable = variable(varName)
            variable.type = "(Array Int Int)"
            return
        }
        val intExpected = intExpectedRe.find(statement)
        if (intExpected != null) {
            val (line, column, argIdx, function) = intExpected.destructured
            val linesTrimmed = trimStatement(smtlib2Statement, line.toInt(), column.toInt())
            val functionPattern = Regex("\\(${Regex.escape(function)}\\s+($VAR_NAME_PATTERN)\\s+($VAR_NAME_PATTERN)\\)")
            val intFunctionCall = functionPattern.find(linesTrimmed)
                ?: error("No int function predicate found")
            val varName = intFunctionCall.groupValues[argIdx.toInt()]
            val variable = variable(varName)
            variable.type = "Int"
            return
        }
        val incompatibleSorts = incompatibleSortsRe.find(statement)
        if (incompatibleSorts != null) {
            incompatibleSorts(incompatibleSorts, smtlib2Statement)
            return
        }
        val incompatibleSorts2 = incompatibleSorts2Re.find(statement)
        if (incompatibleSorts2 != null) {
            incompatibleSorts(incompatibleSorts2, smtlib2Statement)
            return
        }
        TODO()
    }

    private fun incompatibleSorts(incompatibleSorts: MatchResult, smtlib2Statement: String) {
        val (line, column, sort) = incompatibleSorts.destructured
        val linesTrimmed = trimStatement(smtlib2Statement, line.toInt(), column.toInt())
        val varOrCall = "((\\(.*\\))|($VAR_NAME_PATTERN))"
        val eqPattern = Regex("\\(=\\s+$varOrCall\\s+$varOrCall\\)")
        val match = eqPattern.find(linesTrimmed)
            ?: error("Not equality")
        val leftVarName = match.groupValues[3]
        val rightVarName = match.groupValues[6]
        if (leftVarName.isBlank() && rightVarName.isBlank()) {
            error("No Var name found")
        }
        if (leftVarName.isNotBlank()) {
            val leftVar = variable(leftVarName)
            if (leftVar.type != sort) leftVar.type = sort
        }
        if (rightVarName.isNotBlank()) {
            val rightVar = variable(rightVarName)
            if (rightVar.type != sort) rightVar.type = sort
        }
    }

    fun trimStatement(statement: String, line: Int, column: Int): String {
        val lines = statement.lines().take(line).toMutableList()
        lines[lines.lastIndex] = lines.last().take(column + 1)
        val statementBefore = lines.joinToString("\n")
        check(statementBefore.last() == ')') { "No closing parenthesis at the end" }
        val result = buildString {
            var parenthesisCount = 0
            for (ch in statementBefore.reversed()) {
                if (ch == ')') parenthesisCount++
                if (ch == '(') parenthesisCount--
                append(ch)
                if (parenthesisCount == 0) break
            }
            check(parenthesisCount == 0) { "Unmatched parenthesis" }
        }
        return result.reversed()
    }
}

package org.jetbrains.research.kex.smt.z3.utilities

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.Z3Exception
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import org.intellij.lang.annotations.RegExp
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.nameWithoutExtension
import kotlin.io.path.readText
import kotlin.io.path.writeText


@OptIn(ExperimentalPathApi::class)
fun main(args: Array<String>) {
    val options = Options()
        .addOption(Option("f", "file", true, "Z3 asserts").apply { isRequired = true })
        .addOption(
            Option("e", "function-call-extension", true, "Function calls definitions")
                .apply { isRequired = false }
        )

    val parsedArgs = DefaultParser().parse(options, args)
    val file = parsedArgs.getOptionValue("file").let { Paths.get(it) }
    val fcExtensionFile = parsedArgs.getOptionValue("function-call-extension")?.let { Paths.get(it) }
    val smtlib2Source = file.readText()
    val fcExtension = fcExtensionFile?.let { FunctionCallInfo.load(it) }
    val result = guessVariableDeclarations(smtlib2Source, fcExtension)
    file.parent().resolve("${file.fileName.nameWithoutExtension}-with-variables").writeText(result)
}

fun guessVariableDeclarations(smtlib2Source: String, fcExtension: List<FunctionCallInfo>? = null): String {
    val searchContext = SearchContext(smtlib2Source, fcExtension)
    searchContext.loop()
    return searchContext.smtlibWithDeclarations()
}

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

class ErrorMessageAnalyzer(val pattern: Regex, val analyzer: (MatchResult.Destructured, String) -> Unit) {
    fun analyzeIfPossible(message: String, source: String): Boolean {
        val match = pattern.find(message) ?: return false
        analyzer(match.destructured, source)
        return true
    }
}

class SearchContext(val smtlib2Source: String, val functionCallFormulaExtension: List<FunctionCallInfo>?) {
    val z3Context = Context()
    var needFunctionCallDef = false
    val vars = mutableMapOf<String, Var>()

    private val sourceWithFc by lazy {
        val fcExtensions = functionCallFormulaExtension ?: error("No function call info provided")
        val defineStatements = fcExtensions.joinToString("\n") { it.smtlibDeclareStatement() }
        return@lazy "${defineStatements}\n${smtlib2Source}"
    }

    private fun source(): String = if (needFunctionCallDef) sourceWithFc else smtlib2Source

    private val messageAnalyzers = listOf(
        analyzer("\\(error \"line \\d+ column \\d+: unknown function/constant function_call\"\\)") { _, _ ->
            needFunctionCallDef = true
        },
        analyzer("\\(error \"line \\d+ column \\d+: unknown constant (.*)\"\\)") { (varName), _ ->
            variable(varName)
        },
        analyzer(
            "\\(error \"line (\\d+) column (\\d+): store expects the first argument sort to be an array\"\\)"
        ) { (line, column), src ->
            val linesTrimmed = trimStatement(src, line.toInt(), column.toInt())
            val storePattern = Regex("\\(store\\s+($VAR_NAME_PATTERN)\\s+$VAR_NAME_PATTERN\\s+$VAR_NAME_PATTERN\\)")
            val storePredicate = storePattern.find(linesTrimmed)
                ?: error("No store predicate found")
            val varName = storePredicate.groupValues[1]
            val variable = variable(varName)
            variable.type = "(Array Int Int)"
        },
        analyzer(
            "\\(error \"line (\\d+) column (\\d+): Sort mismatch at argument #(\\d+) for function \\(declare-fun (.*) \\(Int Int\\) \\w+\\) supplied sort is Bool\"\\)"
        ) { (line, column, argIdx, function), src ->
            val linesTrimmed = trimStatement(src, line.toInt(), column.toInt())
            val functionPattern = Regex("\\(${Regex.escape(function)}\\s+($VAR_NAME_PATTERN)\\s+($VAR_NAME_PATTERN)\\)")
            val intFunctionCall = functionPattern.find(linesTrimmed)
                ?: error("No int function predicate found")
            val varName = intFunctionCall.groupValues[argIdx.toInt()]
            val variable = variable(varName)
            variable.type = "Int"
        },
        analyzer("\\(error \"line (\\d+) column (\\d+): Sorts Bool and (.*) are incompatible\"\\)") { (line, column, sort), src ->
            incompatibleSorts(line, column, sort, src)
        },
        analyzer("\\(error \"line (\\d+) column (\\d+): Sorts (.*) and Bool are incompatible\"\\)") { (line, column, sort), src ->
            incompatibleSorts(line, column, sort, src)
        },
        analyzer(
            "\\(error \"line (\\d+) column (\\d+): Sort mismatch at argument #(\\d+) for function \\(declare-fun function_call.*"
        ) { (line, column, argIdx), src ->
            val linesTrimmed = trimStatement(src, line.toInt(), column.toInt())
            val functionIdxPattern = Regex("\\(function_call\\s+(\\d+)\\s+")
            val functionIdx = functionIdxPattern.find(linesTrimmed)?.groupValues?.get(1)?.toInt()
                ?: error("No function id found")
            val functionInfo = functionCallFormulaExtension?.find { it.idx == functionIdx }
                ?: error("No function info for idx: $functionIdx")
            val functionCallArgsPattern =
                Regex("\\(function_call\\s+(\\d+)${functionInfo.args.joinToString("") { "\\s+($VAR_NAME_PATTERN)" }}\\)")
            val functionCallArgs = functionCallArgsPattern.find(linesTrimmed)
                ?: error("Function call args pattern error")
            val functionCallArgName = functionCallArgs.groupValues[argIdx.toInt()]
            val functionCallArgDef = functionInfo.args[argIdx.toInt() - 2]
            val variable = variable(functionCallArgName)
            variable.type = functionCallArgDef.type
        }
    )

    fun loop() {
        while (true) {
            try {
                parse()
                return
            } catch (ex: Z3Exception) {
                val message = ex.message?.let { takeGroupsInsideParenthesis(it) } ?: emptyList()
                message.forEach { analyzeMessage(it) }
            }
        }
    }

    private fun parse(): Array<out BoolExpr> {
        val variables = vars.values.toList()
        val symbols = variables.map { it.symbol(z3Context) }.toTypedArray()
        val decls = variables.map { it.funDecl(z3Context) }.toTypedArray()
        return z3Context.parseSMTLIB2String(
            source(),
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

    fun analyzeMessage(statement: String) {
        val statementSource = source()
        if (!messageAnalyzers.any { it.analyzeIfPossible(statement, statementSource) }) {
            error("No analyzer for message: $statement")
        }
    }

    private fun incompatibleSorts(line: String, column: String, sort: String, smtlib2Statement: String) {
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


    companion object {
        fun analyzer(@RegExp pattern: String, analyzer: (MatchResult.Destructured, String) -> Unit) =
            ErrorMessageAnalyzer(Regex(pattern), analyzer)

        fun trimStatement(statement: String, line: Int, column: Int): String {
            val lines = statement.lines().take(line).toMutableList()
            lines[lines.lastIndex] = lines.last().take(column + 1)
            val statementBefore = lines.joinToString("\n")
            check(statementBefore.last() == ')') { "No closing parenthesis at the end" }
            return takeGroupsInsideParenthesis(statementBefore.reversed(), reversed = true).first().reversed()
        }

        fun takeGroupsInsideParenthesis(text: String, reversed: Boolean = false): List<String> {
            val openP = if (!reversed) '(' else ')'
            val closeP = if (!reversed) ')' else '('
            val textGroups = mutableListOf<String>()
            val groupBuilder = StringBuilder()
            var parenthesisCount = 0
            var skip = true
            for (ch in text) {
                if (!skip && ch == closeP) {
                    parenthesisCount--
                }
                if (ch == openP) {
                    parenthesisCount++
                    skip = false
                }
                if (!skip) {
                    groupBuilder.append(ch)
                }
                if (!skip && parenthesisCount == 0) {
                    textGroups += groupBuilder.toString()
                    groupBuilder.clear()
                    skip = true
                }
            }
            return textGroups
        }
    }
}

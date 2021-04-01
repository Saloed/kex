package org.jetbrains.research.kex.smt.z3.utilities

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readText
import kotlin.io.path.writeText

fun main(args: Array<String>) {
    val options = Options()
        .addOption(Option("g", "good", true, "Z3 asserts").apply { isRequired = true })
        .addOption(Option("b", "bad", true, "Z3 asserts").apply { isRequired = true })
        .addOption(
            Option("e", "function-call-extension", true, "Function calls definitions")
                .apply { isRequired = false }
        )
        .addOption(Option("d", "dump", false, "Dump intermediate results").apply { isRequired = false })
    val parsedArgs = DefaultParser().parse(options, args)
    val goodAssertsFile = parsedArgs.getOptionValue("good").let { Paths.get(it) }
    val badAssertsFile = parsedArgs.getOptionValue("bad").let { Paths.get(it) }
    val fcExtensionFile = parsedArgs.getOptionValue("function-call-extension")?.let { Paths.get(it) }
    val fcExtensions = fcExtensionFile?.let { FunctionCallInfo.load(it) }
    val dumpIntermediateResults = parsedArgs.hasOption("dump")
    println("Guess good variables")
    val goodWithVariables = guessVariables(goodAssertsFile, dumpIntermediateResults, fcExtensions)
    println("Guess bad variables")
    val badWithVariables = guessVariables(badAssertsFile, dumpIntermediateResults, fcExtensions)
    println("Tag good variables")
    val goodWithTags = renameVariables(goodAssertsFile, goodWithVariables, VarTag.GOOD, dumpIntermediateResults)
    println("Tag bad variables")
    val badWithTags = renameVariables(badAssertsFile, badWithVariables, VarTag.BAD, dumpIntermediateResults)
    println("Create equality query")
    val equalityCheckerQuery =
        makeEqualityCheckerQuery(goodAssertsFile, goodWithTags, badWithTags, dumpIntermediateResults)
    println("Run equality check")
    val checkResult = checkEquality(goodAssertsFile, equalityCheckerQuery, dumpIntermediateResults, fcExtensions)
    println(checkResult)
}

@OptIn(ExperimentalPathApi::class)
fun checkEquality(
    assertsFile: Path,
    equalityCheckerQuery: String,
    dump: Boolean,
    fcExtension: List<FunctionCallInfo>?
): String {
    val result = checkFormulasEquality(equalityCheckerQuery, fcExtension)
    if (dump) {
        val dumpFile = assertsFile.parent().resolve("${assertsFile.fileName}-result")
        dumpFile.writeText(result)
    }
    return result
}

@OptIn(ExperimentalPathApi::class)
private fun makeEqualityCheckerQuery(assertsFile: Path, good: String, bad: String, dump: Boolean): String {
    val ctx = Context()
    val goodAsserts = ctx.parseSMTLIB2String(good, emptyArray(), emptyArray(), emptyArray(), emptyArray())
    val badAsserts = ctx.parseSMTLIB2String(bad, emptyArray(), emptyArray(), emptyArray(), emptyArray())
    val goodSingleAssert = ctx.mkAnd(*goodAsserts)
    val badSingleAssert = ctx.mkAnd(*badAsserts)
    val result = ctx.printAsserts(listOf(goodSingleAssert, badSingleAssert))
    if (dump) {
        val dumpFile = assertsFile.parent().resolve("${assertsFile.fileName}-equality-query")
        dumpFile.writeText(result)
    }
    return result
}

@OptIn(ExperimentalPathApi::class)
private fun renameVariables(assertsFile: Path, source: String, tag: VarTag, dump: Boolean): String {
    val ctx = Context()
    val asserts = ctx.parseSMTLIB2String(source, emptyArray(), emptyArray(), emptyArray(), emptyArray())
    val variables = asserts.flatMap { collectVariables(it) }.toSet().toList()
    val newVariables = variables.map { ctx.mkConst("${tag.marker}${it.name()}", it.sort) }
    val newAsserts = asserts.map { it.substitute(variables.toTypedArray(), newVariables.toTypedArray()) as BoolExpr }
    val result = ctx.printAsserts(newAsserts)
    if (dump) {
        val dumpFile = assertsFile.parent().resolve("${assertsFile.fileName}-with-tags")
        dumpFile.writeText(result)
    }
    return result
}

@OptIn(ExperimentalPathApi::class)
private fun guessVariables(assertsFile: Path, dump: Boolean, fcExtensions: List<FunctionCallInfo>?): String {
    val source = assertsFile.readText()
    val withVariables = guessVariableDeclarations(source, fcExtensions)
    if (dump) {
        val dumpFile = assertsFile.parent().resolve("${assertsFile.fileName}-with-variables")
        dumpFile.writeText(withVariables)
    }
    return withVariables
}

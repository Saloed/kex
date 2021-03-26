package org.jetbrains.research.kex.smt.z3.utilities

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.enumerations.Z3_ast_kind
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import java.io.Writer
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.*


@ExperimentalPathApi
fun main(args: Array<String>) {
    val options = Options()
        .addOption(Option("l", "left", true, "Z3 asserts to place on left side").apply { isRequired = true })
        .addOption(Option("r", "right", true, "Z3 asserts to place on right side").apply { isRequired = true })

    val parsedArgs = DefaultParser().parse(options, args)
    val leftFile = parsedArgs.getOptionValue("left").let { Paths.get(it) }
    val rightFile = parsedArgs.getOptionValue("right").let { Paths.get(it) }

    val context = Context(mapOf("enable_function_call_support" to "true"))
    val leftAsserts = context.parseSMTLIB2File(
        leftFile.toAbsolutePath().toString(),
        emptyArray(),
        emptyArray(),
        emptyArray(),
        emptyArray()
    )
    val rightAsserts = context.parseSMTLIB2File(
        rightFile.toAbsolutePath().toString(),
        emptyArray(),
        emptyArray(),
        emptyArray(),
        emptyArray()
    )
    val cmpContext = CompareContext(context, leftAsserts, rightAsserts)
    val matches = leftAsserts.indices.associateWith { structureMatchCandidates(cmpContext, it) }
    val (matched, unresolvedLeft, unresolvedRight) = resolveMatchGroups(cmpContext, matches)

    val leftResultFile = leftFile.toResultPath()
    val rightResultFile = rightFile.toResultPath()
    leftResultFile.bufferedWriter().use { leftWriter ->
        rightResultFile.bufferedWriter().use { rightWriter ->
            writeResult(
                leftWriter,
                rightWriter,
                cmpContext,
                matched,
                unresolvedLeft,
                unresolvedRight
            )
        }
    }
}

private fun writeResult(
    leftFile: Writer,
    rightFile: Writer,
    ctx: CompareContext,
    matched: Map<Int, Int>,
    unresolvedLeft: Set<Int>,
    unresolvedRight: Set<Int>
) {
    val orderedMatches = matched.toList().sortedBy { it.first }
    val orderedLeftUnresolved = unresolvedLeft.sortedBy { it }
    val orderedRightUnresolved = unresolvedRight.sortedBy { it }
    for ((left, right) in orderedMatches) {
        leftFile.writeSeparator("-")
        rightFile.writeSeparator("-")
        leftFile.write(ctx.left[left].toString())
        rightFile.write(ctx.right[right].toString())
    }
    for (left in orderedLeftUnresolved) {
        leftFile.writeSeparator("*")
        leftFile.write(ctx.left[left].toString())
    }
    for (right in orderedRightUnresolved) {
        rightFile.writeSeparator("*")
        rightFile.write(ctx.right[right].toString())
    }
}

private fun Writer.writeSeparator(separator: String) = write("\n${separator.repeat(20)}\n")

@ExperimentalPathApi
private fun Path.toResultPath() =
    (parent ?: Path("."))
        .resolve("${fileName.nameWithoutExtension}_ordered.${fileName.extension}")

private fun resolveMatchGroups(
    ctx: CompareContext,
    matches: Map<Int, Set<Int>>
): Triple<Map<Int, Int>, Set<Int>, Set<Int>> {
    val assigment = mutableMapOf<Int, Int>()
    val notAssignedRights = ctx.right.indices.toMutableSet()
    var unresolved: Map<Int, Set<Int>>
    var nextUnresolved = matches
    do {
        do {
            unresolved = nextUnresolved
            nextUnresolved = resolveSingleGroups(unresolved, notAssignedRights, assigment)
                .filterUnresolved(notAssignedRights)
        } while (nextUnresolved != unresolved)
        nextUnresolved = resolveEqualGroups(unresolved, notAssignedRights, assigment)
            .filterUnresolved(notAssignedRights)
    } while (nextUnresolved != unresolved)
    return Triple(assigment, unresolved.keys, notAssignedRights)
}

private fun Map<Int, Set<Int>>.filterUnresolved(notAssignedRights: Set<Int>) =
    mapValues { (_, v) -> v.filter { it in notAssignedRights }.toSet() }

private fun resolveEqualGroups(
    matches: Map<Int, Set<Int>>,
    notAssignedRights: MutableSet<Int>,
    assigment: MutableMap<Int, Int>
): Map<Int, Set<Int>> {
    val unmatched = mutableMapOf<Int, Set<Int>>()
    val grouped = matches.entries.groupBy({ it.value }, { it.key }).mapValues { (_, v) -> v.toSet() }
    for ((rights, lefts) in grouped) {
        if (rights.size == lefts.size) {
            lefts.zip(rights).forEach { (l, r) ->
                assigment[l] = r
                notAssignedRights -= r
            }
            continue
        }
        for (left in lefts) {
            unmatched[left] = (unmatched[left] ?: emptySet()) + rights
        }
    }
    return unmatched
}

private fun resolveSingleGroups(
    matches: Map<Int, Set<Int>>,
    notAssignedRights: MutableSet<Int>,
    assigment: MutableMap<Int, Int>
): Map<Int, Set<Int>> {
    val unmatched = matches.filterValues { it.size != 1 }.toMutableMap()
    val singleGroups = matches.filterValues { it.size == 1 }
        .map { it.key to it.value.first() }
        .groupBy({ it.second }, { it.first })
    for ((right, lefts) in singleGroups) {
        if (lefts.size == 1) {
            assigment[lefts.first()] = right
            notAssignedRights -= right
            continue
        }
        for (left in lefts) {
            unmatched[left] = (unmatched[left] ?: emptySet()) + right
        }
    }
    return unmatched
}

private class CompareContext(val ctx: Context, val left: Array<BoolExpr>, val right: Array<BoolExpr>)

private fun structureMatchCandidates(ctx: CompareContext, left: Int): Set<Int> {
    val result = mutableSetOf<Int>()
    val target = ctx.left[left]
    for ((i, right) in ctx.right.withIndex()) {
        if (structureMatch(target, right)) {
            result += i
        }
    }
    return result
}

private fun structureMatch(left: Expr, right: Expr): Boolean {
    if (left == right) return true
    val leftKind = left.astKind
    val rightKind = right.astKind
    if (leftKind != rightKind) return false
    if (leftKind == Z3_ast_kind.Z3_VAR_AST) return true
    if (leftKind == Z3_ast_kind.Z3_APP_AST) return structureMatchApp(left, right)
    // todo: more kinds
    return false
}

private fun structureMatchApp(left: Expr, right: Expr): Boolean {
    if (left.funcDecl.declKind != right.funcDecl.declKind) return false
    if (left.numArgs != right.numArgs) return false
    if (left.isOr || left.isAdd) return structureMatchAppUnordered(left, right)
    return structureMatchAppOrdered(left, right)
}

fun structureMatchAppOrdered(left: Expr, right: Expr): Boolean {
    val leftArgs = left.args
    val rightArgs = right.args
    for ((li, l) in leftArgs.withIndex()) {
        val r = rightArgs[li]
        if (!structureMatch(l, r)) return false
    }
    return true
}

fun structureMatchAppUnordered(left: Expr, right: Expr): Boolean {
    val takenRights = mutableSetOf<Int>()
    val leftArgs = left.args
    val rightArgs = right.args
    for (l in leftArgs) {
        var matched = false
        for ((ri, r) in rightArgs.withIndex()) {
            if (ri in takenRights) continue
            if (structureMatch(l, r)) {
                takenRights += ri
                matched = true
                break
            }
        }
        if (!matched) return false
    }
    return true
}

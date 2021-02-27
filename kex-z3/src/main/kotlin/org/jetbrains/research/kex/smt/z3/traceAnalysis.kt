package org.jetbrains.research.kex.smt.z3

import com.github.saloed.diff.DiffMode
import com.github.saloed.diff.twoWayDiffFromDMPDiff
import name.fraser.neil.plaintext.DiffMatchPatch
import name.fraser.neil.plaintext.diff_match_patch.Diff
import name.fraser.neil.plaintext.diff_match_patch.Operation
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readLines
import kotlin.io.path.writeText

@ExperimentalPathApi
fun main(args: Array<String>) {
    val options = Options()
        .addOption(Option("l", "left", true, "Z3 trace file to place on left side").apply { isRequired = true })
        .addOption(Option("r", "right", true, "Z3 trace file to place on right side").apply { isRequired = true })
        .addOption(Option("o", "out", true, "Result patch file name").apply { isRequired = true })
    val parsedArgs = DefaultParser().parse(options, args)
    val outFile = parsedArgs.getOptionValue("out").let { Paths.get(it) }
    val leftFile = parsedArgs.getOptionValue("left").let { Paths.get(it) }
    val rightFile = parsedArgs.getOptionValue("right").let { Paths.get(it) }

    val lhsSections = makeSections(leftFile.readLines(Charsets.UTF_8))
    val rhsSections = makeSections(rightFile.readLines(Charsets.UTF_8))

    val leftHeaders = lhsSections.joinToString("\n") { it.header }
    val rightHeaders = rhsSections.joinToString("\n") { it.header }
    val linesDiff = DiffMatchPatch().diffLineLevel(leftHeaders, rightHeaders)
    val headerDiff = makeHeaderDiff(linesDiff)

    val sectionGroups = groupSections(headerDiff, lhsSections, rhsSections)
    check(sectionGroups.filter { it.left != null }.count() == lhsSections.size) { "Left groups mismatch" }
    check(sectionGroups.filter { it.right != null }.count() == rhsSections.size) { "Right groups mismatch" }
    val diffs = sectionGroups.flatMap { it.asDiff() }
    val twoWayDiff = twoWayDiffFromDMPDiff(diffs, leftFile.fileName.toString(), rightFile.fileName.toString(), DiffMode.LINE)
    val result = twoWayDiff.saveToJson()
    outFile.writeText(result, Charsets.UTF_8)
}

private data class HeaderDiff(val left: String?, val right: String?)


data class FileSection(val header: String, val content: List<String>) {
    fun contentString() = content.joinToString(separator = "") { "$it\n" }
    fun toDiff(operation: Operation) = listOf(Diff(operation, contentString()))
}

private data class SectionGroup(val left: FileSection?, val right: FileSection?) {
    fun asDiff(): List<Diff> = when {
        left != null && right != null -> contentDiff(left, right)
        left == null && right != null -> right.toDiff(Operation.INSERT)
        left != null && right == null -> left.toDiff(Operation.DELETE)
        else -> emptyList()
    }
}

private fun contentDiff(left: FileSection, right: FileSection) =
    DiffMatchPatch().diffLineLevel(left.contentString(), right.contentString())

private val headerLineRegex = Regex("^-------- \\[[\\w\\d_-]+\\] .* ---------$")

private fun String.isHeaderLine() = headerLineRegex.matches(this)

private fun Diff.lines() = text.lines().dropLastWhile { it.isEmpty() }

private fun makeHeaderDiff(diff: List<Diff>): List<HeaderDiff> {
    val result = mutableListOf<HeaderDiff>()
    for (diffItem in diff) {
        val headers = diffItem.lines()
        result += headers.map {
            when (diffItem.operation) {
                Operation.EQUAL -> HeaderDiff(it, it)
                Operation.DELETE -> HeaderDiff(it, null)
                Operation.INSERT -> HeaderDiff(null, it)
            }
        }
    }
    return result
}

private fun groupSections(
    diff: List<HeaderDiff>,
    leftSections: List<FileSection>,
    rightSections: List<FileSection>
): List<SectionGroup> {
    val leftIter = leftSections.iterator()
    val rightIter = rightSections.iterator()
    return diff.map { item ->
        val left = item.left?.let { header ->
            leftIter.next().also { check(it.header == header) { "Left header mismatch: $header | ${it.header}" } }
        }
        val right = item.right?.let { header ->
            rightIter.next().also { check(it.header == header) { "Right header mismatch: $header | ${it.header}" } }
        }
        SectionGroup(left, right)
    }
}

private fun makeSections(lines: List<String>): List<FileSection> {
    val sections = mutableListOf<FileSection>()
    var currentHeader = ""
    val currentSectionContent = mutableListOf<String>()
    var firstSection = true
    for (line in lines) {
        val isHeader = line.isHeaderLine()
        if (isHeader && !firstSection) {
            sections += FileSection(currentHeader, currentSectionContent.toList())
            currentHeader = line
            currentSectionContent.clear()
        }
        if (isHeader && firstSection) {
            firstSection = false
            currentHeader = line
            currentSectionContent.clear()
        }
        currentSectionContent += line
    }
    if (currentSectionContent.isNotEmpty()) {
        sections += FileSection(currentHeader, currentSectionContent.toList())
    }
    return sections
}

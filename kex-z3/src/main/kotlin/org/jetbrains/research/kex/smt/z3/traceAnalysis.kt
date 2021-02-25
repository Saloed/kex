package org.jetbrains.research.kex.smt.z3

import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readLines

@ExperimentalPathApi
fun main(args: Array<String>) {
    val options = Options()
        .addOption(Option("l", "left", true, "Z3 trace file to place on left side").apply { isRequired = true })
        .addOption(Option("r", "right", true, "Z3 trace file to place on right side").apply { isRequired = true })
    val parsedArgs = DefaultParser().parse(options, args)
    val lhs = parsedArgs.getOptionValue("left").let { Paths.get(it) }.readLines(Charsets.UTF_8)
    val rhs = parsedArgs.getOptionValue("right").let { Paths.get(it) }.readLines(Charsets.UTF_8)

    val lhsSections = makeSections(lhs)
    val rhsSections = makeSections(rhs)
    val sectionGroups = groupSections(lhsSections, rhsSections)
    check(sectionGroups.filter { it.left != null }.count() == lhsSections.size) { "Left groups mismatch" }
    check(sectionGroups.filter { it.right != null }.count() == rhsSections.size) { "Right groups mismatch" }

    val a = 3
}

private data class FileSection(val header: String, val content: List<String>)

private data class SectionGroup(val left: FileSection?, val right: FileSection?)

private val headerLineRegex = Regex("^-------- \\[[\\w\\d_-]+\\] .* ---------$")

private fun String.isHeaderLine() = headerLineRegex.matches(this)

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

private const val MATCH_SEARCH_WINDOW = 10

private fun groupSections(left: List<FileSection>, right: List<FileSection>): List<SectionGroup> {
    val groups = mutableListOf<SectionGroup>()
    var leftIdx = 0
    var rightIdx = 0
    while (leftIdx < left.size || rightIdx < right.size) {
        if (leftIdx == left.size) {
            groups += SectionGroup(null, right[rightIdx])
            rightIdx++
            continue
        }
        if (rightIdx == right.size) {
            groups += SectionGroup(left[leftIdx], null)
            leftIdx++
            continue
        }
        if (left[leftIdx].header == right[rightIdx].header) {
            groups += SectionGroup(left[leftIdx], right[rightIdx])
            leftIdx++
            rightIdx++
            continue
        }
        val rightMatchIdx = searchInWindow(left[leftIdx], rightIdx, right)
        val leftMatchIdx = searchInWindow(right[rightIdx], leftIdx, left)
        if (rightMatchIdx == null && leftMatchIdx == null) {
            groups += SectionGroup(null, right[rightIdx])
            groups += SectionGroup(left[leftIdx], null)
            leftIdx++
            rightIdx++
            continue
        }
        if (rightMatchIdx == null || leftMatchIdx != null && leftMatchIdx - leftIdx <= rightMatchIdx - rightIdx) {
            // match future record from left to current right
            while (leftIdx < leftMatchIdx!!) {
                groups += SectionGroup(left[leftIdx], null)
                leftIdx++
            }
            groups += SectionGroup(left[leftIdx], right[rightIdx])
            leftIdx++
            rightIdx++
            continue
        } else {
            // match future record from right to current left
            while (rightIdx < rightMatchIdx) {
                groups += SectionGroup(null, right[rightIdx])
                rightIdx++
            }
            groups += SectionGroup(left[leftIdx], right[rightIdx])
            leftIdx++
            rightIdx++
            continue
        }
    }
    return groups
}

private fun searchInWindow(target: FileSection, startIdx: Int, sections: List<FileSection>): Int? {
    var idx = startIdx
    while (idx < minOf(startIdx + MATCH_SEARCH_WINDOW, sections.size)) {
        if (sections[idx].header == target.header) return idx
        idx++
    }
    return null
}

package org.jetbrains.research.kex.refinements

import kotlin.test.Test


class CyclesRefinementTest : RefinementTest("Cycles") {
    @Test
    fun testCycle() = run("cycle") {
        refinementFromResource(IllegalArgumentException())
    }
}
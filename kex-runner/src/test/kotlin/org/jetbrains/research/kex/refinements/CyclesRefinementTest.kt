package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Test

class CyclesRefinementTest : RefinementTest("Cycles") {
    @Test
    fun testCycle() = run("cycle") {
        refinement(IllegalArgumentException()) { emptyState() }
    }
}
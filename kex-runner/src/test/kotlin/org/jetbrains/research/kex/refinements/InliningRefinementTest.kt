package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Test

class InliningRefinementTest : RefinementTest("Inlining") {
    @Test
    fun testDeepInlining() = run("deepInlining") {
        refinement(IllegalArgumentException()) {
            emptyState()
        }
    }
}
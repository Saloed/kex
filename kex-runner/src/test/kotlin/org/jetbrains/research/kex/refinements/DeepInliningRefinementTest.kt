package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Test

class DeepInliningRefinementTest : RefinementTest("DeepInlining") {
    @Test
    fun testDeepInlining() = run("deepInlineTest") {
        refinement(IllegalArgumentException()) {
            emptyState()
        }
        refinement(IllegalStateException()) {
            emptyState()
        }
    }
}
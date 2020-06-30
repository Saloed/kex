package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.trueState
import kotlin.test.Test

class InliningRefinementTest : RefinementTest("Inlining") {
    @Test
    fun testDeepInlining() = run("deepInlining") {
        refinement(IllegalArgumentException()) {
            emptyState()
        }
    }

    @Test
    fun testExceptionSourceInlining() = run("inlineExceptionSource"){
        refinement(null) {
            trueState()
        }
        refinement(IllegalStateException()) {
            trueState()
        }
    }
}

package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.choice
import kotlin.test.Test

class DeepInliningRefinementTest : RefinementTest("DeepInlining") {
    @Test
    fun testDeepInlining() = run("deepInlineTest") {
        refinement(IllegalArgumentException()) {
            basic {
                path { arg(KexInt(), 1) lt arg(KexInt(), 0) equality true }
            }
        }
        refinement(IllegalStateException()) {
            choice({
                path { arg(KexInt(), 0) lt const(0) equality true }
            }, {
                path { arg(KexInt(), 1) gt const(100) equality true }
            }, {
                path { arg(KexInt(), 2) lt const(0) equality true }
            })
        }
    }
}
package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexArray
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.choice
import org.jetbrains.research.kex.state.emptyState
import org.junit.jupiter.api.Test

class ArraysRefinementTest : RefinementTest("Arrays") {
    @Test
    fun testArray() = run("arrayTest") {
        refinement(ArrayIndexOutOfBoundsException()) {
            choice({
                path {
                    arg(KexInt(), 1) lt const(0) equality const(true)
                }
            }, {
                path {
                    arg(KexInt(), 1) ge arg(KexArray(KexInt()), 1).length() equality const(true)
                }
            })
        }
        refinement(IllegalArgumentException()) { emptyState() }
    }
}
package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Test

class UnknownsRefinementTest : RefinementTest("Unknowns") {
    @Test
    fun testUnknownSimple() = run("unknownSimple") {
        refinement(IllegalStateException()) { emptyState() }
    }

    @Test
    fun testUnknownFunctionCall() = run("unknownFunctionCall") {
        refinement(IllegalStateException()) { emptyState() }
    }

    @Test
    fun testRecursiveUnknownFunction() = run("recursiveUnknownFunction") {
        refinement(IllegalArgumentException()) { emptyState() }
    }
} 
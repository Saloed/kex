package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Ignore
import kotlin.test.Test

@Ignore
class UnknownsRefinementTest : RefinementTest("Unknowns") {
    @Test
    fun testUnknownSimple() = run("unknownSimple") {
        refinementFromResource(IllegalStateException())
    }

    @Test
    fun testUnknownFunctionCall() = run("unknownFunctionCall") {
        refinementFromResource(IllegalStateException())
    }

    @Test
    fun testRecursiveUnknownFunction() = run("recursiveUnknownFunction") {}

    @Test
    fun testUnknownInterfaceMethods() = run("unknownInterfaceMethods") {
        refinement(IllegalArgumentException()) {
            emptyState()
        }
    }
}

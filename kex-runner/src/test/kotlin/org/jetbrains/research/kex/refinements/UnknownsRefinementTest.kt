package org.jetbrains.research.kex.refinements

import kotlinx.serialization.ImplicitReflectionSerializer
import kotlin.test.Test

class UnknownsRefinementTest : RefinementTest("Unknowns") {
    @Test
    @ImplicitReflectionSerializer
    fun testUnknownSimple() = run("unknownSimple") {
        refinementFromResource(IllegalStateException())
    }

    @Test
    @ImplicitReflectionSerializer
    fun testUnknownFunctionCall() = run("unknownFunctionCall") {
        refinementFromResource(IllegalStateException())
    }

    @Test
    fun testRecursiveUnknownFunction() = run("recursiveUnknownFunction") {}
}

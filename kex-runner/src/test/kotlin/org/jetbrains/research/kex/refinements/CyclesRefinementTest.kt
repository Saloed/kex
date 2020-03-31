package org.jetbrains.research.kex.refinements

import kotlinx.serialization.ImplicitReflectionSerializer
import kotlin.test.Test


class CyclesRefinementTest : RefinementTest("Cycles") {
    @Test
    @ImplicitReflectionSerializer
    fun testCycle() = run("cycle") {
        refinementFromResource(IllegalArgumentException())
    }
}
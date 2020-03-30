package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Test

class ClassesRefinementTest : RefinementTest("Classes") {

    @Test
    fun testMutablePropertyAndLocalObject() = run("mutablePropertyAndLocalObject") {
        refinement(IllegalArgumentException()) { emptyState() }
    }

    @Test
    fun testMutablePropertyAndLocalObjectSmall() = run("mutablePropertyAndLocalObjectSmall") {
        refinement(IllegalArgumentException()) { emptyState() }
    }

    @Test
    fun testMutableProperty() = run("mutableProperty") {
        refinement(IllegalArgumentException()) { emptyState() }
    }

    @Test
    fun testManyClassArgs() = run("manyClassArgs") {
        refinement(IllegalArgumentException()) { emptyState() }
    }

    @Test
    fun testUnusedArgs() = run("unusedArgs") {
        refinement(IllegalArgumentException()) { emptyState() }
    }

    @Test
    fun testComplex() = run("complex") {
        refinement(IllegalArgumentException()) { emptyState() }
        refinement(IllegalStateException()) { emptyState() }
    }
}
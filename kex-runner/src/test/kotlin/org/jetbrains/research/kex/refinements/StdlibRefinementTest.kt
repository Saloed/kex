package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Ignore
import kotlin.test.Test

@Ignore
class StdlibRefinementTest : RefinementTest("Stdlib", includeStdlib = true, failOnError = false) {
    @Test
    fun testUnsafeFirstInt() = run("unsafeFirstInt") {
        refinement(NoSuchElementException()) {
            emptyState()
        }
    }

    @Test
    fun testUnsafeFirstStr() = run("unsafeFirstStr") {
        refinement(NoSuchElementException()) {
            emptyState()
        }
    }

    @Test
    fun testUnsafeFirstBool() = run("unsafeFirstBool") {
        refinement(NoSuchElementException()) {
            emptyState()
        }
    }

    @Test
    fun debug(){
        val method = cm["kotlin/collections/CollectionsKt___CollectionsKt"]
                .getMethods("first")
                .first { it.argTypes.size == 1 && it.argTypes[0].name == "java/util/List" }
        val refinements = refinementsForMethod(method)
    }
}
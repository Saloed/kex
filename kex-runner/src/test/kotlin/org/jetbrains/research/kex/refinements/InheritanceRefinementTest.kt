package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.choice
import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Test

class InheritanceRefinementTest : RefinementTest("Inheritance") {
    val positiveCheck = nestedClass("PositiveCheck")
    val negativeCheck = nestedClass("NegativeCheck")
    val checker = nestedClass("Checker")

    @Test
    fun testInterfaceInlining() = run("interfaceInlining") {
        refinement(IllegalArgumentException()) {
            choice({
                path {
                    arg(KexInt(), 1) eq const(0) equality const(true)
                }
            }, {
                path {
                    tf.getInstanceOf(KexClass(positiveCheck), arg(KexClass(checker), 0)) equality const(true)
                }
                path {
                    arg(KexInt(), 1) ge const(0) equality const(true)
                }
            }, {
                path {
                    tf.getInstanceOf(KexClass(negativeCheck), arg(KexClass(checker), 0)) equality const(true)
                }
                path {
                    arg(KexInt(), 1) le const(0) equality const(true)
                }
            })
        }
    }
}
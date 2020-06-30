package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexArray
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.choice
import org.jetbrains.research.kex.state.emptyState
import kotlin.test.Test

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
                    arg(KexInt(), 1) ge arg(KexArray(KexInt(), memspace = 1), 0).length() equality const(true)
                }
            })
        }
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    val array = arg(KexArray(KexInt(), memspace = 1), 0)
                    val index = tf.getArrayIndex(array, arg(KexInt(), 1))
                    tf.getArrayLoad(index) lt const(0) equality const(true)
                }
            }
        }
    }

    @Test
    fun testManyArrays() = run("arrayTest2"){
        refinement(IllegalArgumentException()) { emptyState()}
    }
}
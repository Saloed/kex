package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.*
import kotlin.test.Ignore
import kotlin.test.Test

class SimpleRefinementTest : RefinementTest("Simple") {
    @Test
    fun testSimpleNoReturn() = run("simpleNoReturn") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 0) le const(0) equality const(true)
                }
            }
        }
    }

    @Test
    fun testSimpleWithReturn() = run("simpleWithReturn") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 0) le const(0) equality const(true)
                }
            }
        }
    }

    @Test
    fun testSimpleUnusedUnknown() = run("simpleUnusedUnknown") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 0) lt const(0) equality const(true)
                }
            }
        }
    }

    @Test
    fun testSimpleNestedCall() = run("simpleNestedCall") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 0) le const(0) equality const(true)
                }
            }
        }
    }

    @Test
    fun testSimpleNestedCallAndUnusedUnknown() = run("simpleNestedCallAndUnusedUnknown") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 0) le const(0) equality const(true)
                }
            }
        }
    }

    @Test
    fun testSimpleExceptionOnNestedCallResult() = run("simpleExceptionOnNestedCallResult") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 0) le const(17) equality const(true)
                }
            }
        }
    }

    @Ignore
    @Test
    fun testFloatsAndDoubles() = run("floatsAndDoubles") {
        refinement(IllegalArgumentException()) { emptyState() }
    }

    @Test
    fun testManyExceptionSources() = run("simpleManyExceptionSources") {
        refinement(IllegalStateException()) {
            choice({
                path { arg(KexInt(), 0) lt const(0) equality true }
            }, {
                path { arg(KexInt(), 0) gt const(0) equality true }
            })
        }
    }

    @Test
    fun `test always exception`() = run("alwaysException") {
        refinement(IllegalStateException()) {
            trueState()
        }
    }

    @Test
    fun `test one exception shadowed by another`() = run("shadowedExceptions") {
        refinement(IllegalStateException()) {
            trueState()
        }
    }

    @Test
    fun `test one exception shadowed by exception from call`() = run("shadowedExceptionWithCall") {
        refinement(IllegalStateException()) {
            trueState()
        }
        refinement(IndexOutOfBoundsException()) {
            falseState() // shadowed
        }
        refinement(IllegalArgumentException()) {
            falseState() // shadowed
        }
    }
}
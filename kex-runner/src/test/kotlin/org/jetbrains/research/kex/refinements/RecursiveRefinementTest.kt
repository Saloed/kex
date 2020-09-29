package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.choice
import org.jetbrains.research.kex.state.trueState
import kotlin.test.Test

class RecursiveRefinementTest : RefinementTest("Recursive") {
    private val xcls = KexClass(nestedClass("XCls"))

    @Test
    fun testRecursiveSimple() = run("recursiveSimple") {
        refinement(IllegalArgumentException()) {
            choice({
                path {
                    arg(KexInt(), 0) lt const(17) equality const(true)
                }
            }, {
                path {
                    arg(KexInt(), 0) ge arg(KexInt(), 1) equality const(true)
                }
            })
        }
    }

    @Test
    fun testRecursiveWithNestedCalls() = run("recursiveWithNestedCalls") {
        refinement(IllegalArgumentException()) {
            choice({
                path {
                    arg(KexInt(), 0) lt const(17) equality const(true)
                }
            }, {
                path {
                    arg(KexInt(), 0) ge arg(KexInt(), 1) equality const(true)
                }
            })
        }
    }

    @Test
    fun testRecursiveAlwaysException() = run("recursiveAlwaysException") {
        refinement(IllegalArgumentException()) { trueState() }
    }

    @Test
    fun testRecursiveWithStackOverflow() = run("recursiveWithStackOverflow") {}

    @Test
    fun testRecursiveFunctionCall() = run("recursiveFunctionCall") {
        refinement(IllegalArgumentException()) {
            choice({
                path {
                    arg(KexInt(), 0) le const(100) equality const(true)
                }
            }, {
                path {
                    arg(KexInt(), 0) ge arg(KexInt(), 1) equality const(true)
                }
            })
        }
    }

    @Test
    fun testRecursiveWithMemory() = run("recursiveWithMemory") {
        refinement(IllegalArgumentException()) {
            val choices = listOf(
                    basic {
                        path {
                            arg(xcls, 0).field(KexInt(), "clsFieldB", xcls).load() lt const(0) equality const(true)
                        }
                    },
                    basic {
                        path {
                            arg(xcls, 1).field(KexInt(), "clsFieldA", xcls).load() lt const(0) equality const(true)
                        }
                    },
                    basic {
                        path {
                            arg(xcls, 0).field(KexInt(), "clsFieldA", xcls).load() lt const(17) equality const(true)
                        }
                    },
                    basic {
                        path {
                            arg(xcls, 1).field(KexInt(), "clsFieldB", xcls).load() le arg(xcls, 0).field(KexInt(), "clsFieldA", xcls).load() equality const(true)
                        }
                    }
            )
            ChoiceState(choices)
        }
    }

} 

package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.*
import kotlin.test.Test

class RecursiveRefinementTest : RefinementTest("Recursive") {
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

    val xcls = "$refinementsPackageName/Recursive\$XCls"

    @Test
    fun testRecursiveWithMemory() = run("recursiveWithMemory") {
        refinement(IllegalArgumentException()) {
            val choices = listOf(
                    basic {
                        path {
                            arg(KexClass(xcls), 0).field(KexInt(), "clsFieldB").load() lt const(0) equality const(true)
                        }
                    },
                    basic {
                        path {
                            arg(KexClass(xcls), 1).field(KexInt(), "clsFieldA").load() lt const(0) equality const(true)
                        }
                    },
                    basic {
                        path {
                            arg(KexClass(xcls), 0).field(KexInt(), "clsFieldA").load() lt const(17) equality const(true)
                        }
                    },
                    basic {
                        path {
                            arg(KexClass(xcls), 1).field(KexInt(), "clsFieldB").load() le arg(KexClass(xcls), 0).field(KexInt(), "clsFieldA").load() equality const(true)
                        }
                    }
            )
            ChoiceState(choices)
        }
    }

} 
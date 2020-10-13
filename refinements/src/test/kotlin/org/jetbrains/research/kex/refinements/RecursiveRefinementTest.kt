package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.*
import kotlin.test.Test

class RecursiveRefinementTest : RefinementTest("Recursive") {
    private val xcls = KexClass(nestedClass("XCls"))
    private val immutableIntWrapper = KexClass(nestedClass("ImmutableIntWrapper"))
    private val mutableIntWrapper = KexClass(nestedClass("MutableIntWrapper"))


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

    @Test
    fun `recursion with mutable memory simple`() = run("simpleRecursionWithMutableMemory") {
        refinement(IllegalStateException()) {
            choice({
                path { arg(KexInt(), 1) lt 0 equality true }
            }, {
                path { arg(mutableIntWrapper, 0).field(KexInt(), "value", mutableIntWrapper).load() + arg(KexInt(), 1) ge 20 equality true }
            }).withMemoryVersions()
        }
    }

    @Test
    fun `recursion with immutable memory simple`() = run("simpleRecursionWithImmutableMemory") {
        refinement(IllegalStateException()) {
            choice({
                path { arg(KexInt(), 1) lt 0 equality true }
            }, {
                path { arg(immutableIntWrapper, 0).field(KexInt(), "value", immutableIntWrapper).load() + arg(KexInt(), 1) ge 20 equality true }
            }).withMemoryVersions()
        }
    }
} 

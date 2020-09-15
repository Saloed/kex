package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.choice
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.trueState
import kotlin.test.Test

class InliningRefinementTest : RefinementTest("Inlining") {
    @Test
    fun testDeepInlining() = run("deepInlining") {
        refinement(IllegalArgumentException()) {
            emptyState()
        }
    }

    @Test
    fun testSample() = run("sample") {
        val firstArg = term { arg(KexInt(), 0) }
        val sampleCls = KexClass(nestedClass("SampleCls"))
        val secondArg = term { arg(sampleCls, 1) }
        refinement(IllegalStateException()) {
            choice({
                path {
                    firstArg - secondArg.field(KexInt(), "x").load() gt const(1) equality true
                }
            }, {
                path {
                    firstArg - secondArg.field(KexInt(), "x").load() lt const(1) equality true
                }
                path {
                    firstArg gt const(6) equality true
                }
            }).withMemoryVersions()
        }
    }

    @Test
    fun testExceptionSourceInlining() = run("inlineExceptionSource") {
        refinement(null) {
            trueState()
        }
        refinement(IllegalStateException()) {
            trueState()
        }
    }

    @Test
    fun testInlineWithResultDependency() = run("inlineWithResultDependency") {
        refinement(IllegalStateException()) {
            choice({
                path { arg(KexInt(), 0) lt const(0) equality true }
            }, {
                path { arg(KexInt(), 0) gt const(0) equality true }
            })
        }
    }

    @Test
    fun testInlineWithResultDependency2() = run("inlineWithResultDependency2") {
        refinement(IllegalStateException()) {
            basic {
                path { arg(KexInt(), 0) ge const(0) equality true }
            }
        }
    }
}

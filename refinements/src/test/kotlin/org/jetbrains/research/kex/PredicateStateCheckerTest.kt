package org.jetbrains.research.kex

import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.term.term
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

class PredicateStateCheckerTest : KexTest() {
    private fun run(first: PredicateStateWithPath, second: PredicateStateWithPath) =
            PredicateStateChecker(cm.type).check(first, second)

    @Test
    fun testEqual() {
        val a = term { value(KexInt(), "a") }
        val x = term { value(KexBool(), "x") }
        val first = PredicateStateWithPath(emptyState(), basic {
            path { a ge const(0) equality true }
        })
        val second = PredicateStateWithPath(basic {
            state { a ge const(0) equality x }
        }, basic {
            path { x equality true }
        })
        assertTrue(run(first, second))
    }

    @Test
    fun testNotEqual() {
        val a = term { value(KexInt(), "a") }
        val x = term { value(KexBool(), "x") }
        val first = PredicateStateWithPath(emptyState(), basic {
            path { a ge const(0) equality true }
        })
        val second = PredicateStateWithPath(basic {
            state { a ge const(1) equality x }
        }, basic {
            path { x equality true }
        })
        assertFalse(run(first, second))
    }

    @Test
    fun `test false state not equal`() {
        val a = term { value(KexInt(), "a") }
        val first = PredicateStateWithPath(emptyState(), basic {
            path { a ge const(0) equality true }
        })
        val second = PredicateStateWithPath(falseState(), falseState())
        assertFalse(run(first, second))
    }

    @Test
    fun `test actual and expected impossible`() {
        val first = PredicateStateWithPath(falseState(), falseState())
        val second = PredicateStateWithPath(falseState(), trueState())
        assertNotEquals(first, second)
        assertTrue(run(first, second))
    }
}

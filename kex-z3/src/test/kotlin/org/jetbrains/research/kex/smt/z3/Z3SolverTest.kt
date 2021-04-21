package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Status
import org.jetbrains.research.kex.KexTest
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.memory.*
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class Z3SolverTest : KexTest() {
    @Test
    fun testRunnable() {
        val ef = Z3ExprFactory()

        val a = ef.makeInt("a")
        val b = ef.makeInt("b")
        val c = ef.makeInt("c")

        val zero = ef.makeIntConst(0)
        val one = ef.makeIntConst(1)

        val query = c neq zero

        val state = c eq (ef.if_<Int_>(a gt b).then_(zero).else_(one))

        val ctx = ef.ctx
        val solver = ctx.mkSolver()
        solver.add(query.asAxiom() as BoolExpr)
        solver.add(state.asAxiom() as BoolExpr)

        val res = solver.check()
        assertEquals(Status.SATISFIABLE, res)
    }

    @Test
    fun testDefaultMemory() {
        val ef = Z3ExprFactory()
        val checkExpr = { e: Dynamic_ ->
            val solver = ef.ctx.mkSolver()
            solver.add(e.axiom as BoolExpr)
            solver.add(Z3Engine.negate(ef.ctx, e.expr) as BoolExpr)
            solver.check() == Status.UNSATISFIABLE
        }

        val memory = ef.makeDefaultMemory<Word_>("mem", 0xFF, Word_::class)
        for (i in 0..128) {
            assertTrue(checkExpr(memory[ef.makePtrConst(i)] eq Word_.makeConst(ef.ctx, 0xFF)))
        }
    }

    @Test
    fun testMergeMemory() {
        class AnyMemoryAccess(
            override val scopeInfo: MemoryAccessScope = MemoryAccessScope.RootScope,
            override val memoryVersion: MemoryVersion = MemoryVersion.initial()
        ) : MemoryAccess<Any> {
            override val memoryType: MemoryType = MemoryType.SPECIAL
            override val memorySpace: Int = 0
            override val memoryName: String = "memory"
            override val accessType: MemoryAccessType = MemoryAccessType.WRITE
            override val memoryValueType: KexType = KexInt()
            override fun withScopeInfo(scopeInfo: MemoryAccessScope) =
                AnyMemoryAccess(scopeInfo, memoryVersion)

            override fun withMemoryVersion(memoryVersion: MemoryVersion) =
                AnyMemoryAccess(scopeInfo, memoryVersion)
        }

        val memoryAccess = AnyMemoryAccess()
        val ef = Z3ExprFactory()

        val default = Z3Context(ef, (1 shl 16) + 1, (2 shl 16) + 1)
        default.initialize(listOf(memoryAccess))
        default.resetMemory()

        val memA = default.splitMemory()
        val memB = default.splitMemory()

        val ptr = ef.makePtr("ptr")
        val a = ef.makeIntConst(0xDEAD)
        val b = ef.makeIntConst(0xBEEF)
        val z = ef.makeIntConst(0xABCD)

        val cond = ef.makeInt("cond")
        val condA = cond eq a
        val condB = cond eq b

        memA.writeMemory(ptr, a, memoryAccess, Z3ExprFactory.getType(KexInt()))
        memB.writeMemory(ptr, b, memoryAccess, Z3ExprFactory.getType(KexInt()))

        default.mergeMemory(
            "merged", mapOf(
                condA to memA,
                condB to memB
            )
        )
        val mergedVersion = MemoryVersion.merge(
            listOf(
                memoryAccess.memoryVersion,
                memoryAccess.memoryVersion.increaseSubversion(),
                memoryAccess.memoryVersion.increaseSubversion()
            )
        )
        val mergedAccess = memoryAccess.withMemoryVersion(mergedVersion)

        val c = default.readMemory<Int_>(ptr, mergedAccess, Z3ExprFactory.getType(KexInt()))
        val checkExprIn = { e: Bool_, `in`: Dynamic_ ->
            val solver = ef.ctx.mkSolver()
            solver.add(`in`.asAxiom() as BoolExpr)

            val pred = ef.makeBool("\$CHECK$")
            val ptrll = ef.makePtr("ptrll")
            solver.add((ptrll eq c).asAxiom() as BoolExpr)
            solver.add((pred implies !e).asAxiom() as BoolExpr)

            val prede = pred.expr
            val res = solver.check(prede)
            res == Status.UNSATISFIABLE
        }

        assertTrue(checkExprIn(c eq a, cond eq a))
        assertTrue(checkExprIn(c eq b, cond eq b))
        assertFalse(checkExprIn(c eq a, cond eq z))
    }

    @Test
    fun testLogic() {
        val ctx = Z3EngineContext.normal()

        val checkExpr = { expr: Bool_ ->
            val solver = ctx.mkSolver()
            solver.add(expr.axiom as BoolExpr)
            solver.add(ctx.mkNot(expr.expr as BoolExpr))
            solver.check() == Status.UNSATISFIABLE
        }

        val `true` = Bool_.makeConst(ctx, true)
        val `false` = Bool_.makeConst(ctx, false)

        assertTrue(checkExpr(!(`true` and `false`)))
        assertTrue(checkExpr(`true` or `false`))
        assertTrue(checkExpr(!(`true` eq `false`)))
        assertTrue(checkExpr(`true` neq `false`))

        val a = Word_.makeConst(ctx, 0xFF)
        val b = Word_.makeConst(ctx, 0xFF)
        assertTrue(checkExpr(a eq b))

        val d = Long_.makeConst(ctx, 0xFF)
        val e = Word_.makeConst(ctx, 0xFF)
        assertTrue(checkExpr(d eq e))
    }
}

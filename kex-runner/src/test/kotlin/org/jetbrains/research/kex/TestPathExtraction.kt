package org.jetbrains.research.kex

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.refinements.createPathCondition
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.choice
import org.jetbrains.research.kex.state.memory.MemoryVersioner
import org.jetbrains.research.kex.state.not
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.util.VariableGenerator
import kotlin.test.Test

class TestPathExtraction : KexTest() {
    class PSContext {
        val variables = arrayListOf<Term>()
        fun makeVar(name: String, type: KexType) = term { value(type, name) }.also { variables.add(it) }
    }

    private fun run(builder: PSContext.() -> PredicateState) {
        val context = PSContext()
        val originalState = context.builder()
        val (state, positivePath) = createPathCondition(originalState, VariableGenerator("x"))
        val negativePath = positivePath.not()
        val memoryVersioner = MemoryVersioner()
        val stateWithMemory = memoryVersioner.apply(state)
        log.debug("State: $stateWithMemory")
        log.debug("Positive: $positivePath")
        log.debug("Negative: $negativePath")
        val solver = Z3FixpointSolver(cm.type)
        val answer = solver.refineWithFixpointSolver(stateWithMemory, positivePath, negativePath, context.variables, memoryVersioner.memoryInfo())
        assert(answer is FixpointResult.Sat) { answer }
        log.debug("Result: ${(answer as FixpointResult.Sat).result}")
    }


    @Test
    fun sample0() = run {
        val a = makeVar("a", KexInt())
        val b = makeVar("b", KexInt())
        ChainState(choice({
            path { a le const(16) equality const(false) }
        }, {
            path { b ge const(0) equality const(false) }
        }), choice({
            path { b ge const(0) equality const(false) }
        }, {
            path { a ge const(18) equality const(false) }
        }))
    }
}
package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.exceptions

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

class ExceptionSourceBuilder(val method: Method, val sources: List<ExceptionSource>) {
    private val stateBuilder = PredicateStateBuilderWithThrows.forMethod(method)
    private val sourceByInstruction = sources.associateBy { it.instruction }

    fun build() {
        val nonEmptySources = sources.filterNot { it.path.pc.isEmpty() }
        if (nonEmptySources.isEmpty()) return

        nonEmptySources.map { buildForSource(it) }
    }

    private fun buildForSource(source: ExceptionSource) {
        val state = stateForSource(source)
        val x = 3
    }

    private fun stateForSource(source: ExceptionSource): PredicateState {
        val state = stateBuilder.getInstructionState(source.instruction)
                ?: error("No state for source: $source")
        return state
                .filter { it.mayAffectSourcePath() }
                .filter { source.instruction != it.instruction }
    }

    private fun Predicate.mayAffectSourcePath(): Boolean {
        if (type == PredicateType.Path()) return true
        if (this is ThrowPredicate) return true
        if (this is CallPredicate) return true
        return false
    }

    private val Predicate.instruction: Instruction?
        get() = when (this) {
            is ThrowPredicate -> inst
            is CallPredicate -> callTerm.instruction
            else -> null
        }

}

package org.jetbrains.research.kex.refinements.analyzer.exceptions

import org.jetbrains.research.kex.asm.state.PredicateStateBuilder
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.Instruction

class PredicateStateBuilderWithThrows(method: Method) : PredicateStateBuilder(method) {
    override val predicateBuilder = PredicateBuilderWithThrows(method.cm)
    fun findPredicateForInstruction(inst: Instruction): Predicate =
            predicateBuilder.predicateMap[inst] ?: error("No predicate for instruction: $inst")

    fun blocksBeforeInstruction(inst: Instruction) = order.dropLastWhile { inst !in it }.dropLast(1)

    companion object {
        fun forMethod(method: Method) = PredicateStateBuilderWithThrows(method).apply { init() }
    }
}

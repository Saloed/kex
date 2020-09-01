package org.jetbrains.research.kex.asm.analysis.refinements.solver

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate

interface SolverQuery<T : SolverQuery<T, R>, R> {
    val iteration: Int
    fun updateIteration(updater: (Int) -> Int): T
    fun transform(transformer: (PredicateState) -> PredicateState): T
    fun updateIgnoredCalls(transformer: (Set<CallPredicate>) -> Set<CallPredicate>): T
    fun acceptMemoryCorrector(corrector: (PredicateState, MemoryVersionInfo) -> Pair<PredicateState, MemoryVersionInfo>): T
    fun run(solver: FixpointSolver): R
}

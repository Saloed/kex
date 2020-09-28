package org.jetbrains.research.kex.asm.analysis.refinements.solver

import com.abdullin.kthelper.logging.debug
import com.abdullin.kthelper.logging.log
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.query.V2SimpleFixpointSolverQuery
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate

@Serializable
@SerialName("RefinementsSolverQuery")
data class RefinementsSolverQuery(
        val state: PredicateState,
        val normals: PredicateState,
        val sources: List<PredicateState>,
        val ignoredCalls: Set<CallPredicate>,
        val memoryVersionInfo: MemoryVersionInfo,
        override val iteration: Int
) : SolverQuery<RefinementsSolverQuery, List<RecoveredModel>> {
    override fun transform(transformer: (PredicateState) -> PredicateState) =
            RefinementsSolverQuery(transformer(state), transformer(normals), sources.map(transformer), ignoredCalls, memoryVersionInfo, iteration)

    override fun updateIgnoredCalls(transformer: (Set<CallPredicate>) -> Set<CallPredicate>) =
            RefinementsSolverQuery(state, normals, sources, transformer(ignoredCalls), memoryVersionInfo, iteration)

    override fun acceptMemoryCorrector(corrector: (PredicateState, MemoryVersionInfo) -> Pair<PredicateState, MemoryVersionInfo>): RefinementsSolverQuery {
        val (newState, newMemoryVersionInfo) = corrector(state, memoryVersionInfo)
        return RefinementsSolverQuery(newState, normals, sources, ignoredCalls, newMemoryVersionInfo, iteration)
    }

    override fun updateIteration(updater: (Int) -> Int) =
            RefinementsSolverQuery(state, normals, sources, ignoredCalls, memoryVersionInfo, updater(iteration))

    override fun run(solver: FixpointSolver): List<RecoveredModel> {
        log.debug(this@RefinementsSolverQuery)
        val result = solver.query(
                {
                    it.dumpQuery(this@RefinementsSolverQuery, debug = true)
                    MemoryUtils.verifyVersions(state)
                    query { V2SimpleFixpointSolverQuery(state, sources, normals, ignoredCalls, memoryVersionInfo) }
                },
                { ex ->
                    dumpQuery(this@RefinementsSolverQuery)
                    throw IllegalStateException("$ex")
                }
        )
        log.debug(result)
        return result
    }
}

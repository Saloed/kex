package org.jetbrains.research.kex.refinements.solver

import org.jetbrains.research.kthelper.logging.debug
import org.jetbrains.research.kthelper.logging.log
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.query.RefineFixpointSolverQuery
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.Term

@Serializable
@SerialName("CallResolveSolverQuery")
data class CallResolveSolverQuery(
        val state: PredicateState,
        val positivePath: PredicateState,
        val negativePath: PredicateState,
        val arguments: List<Term>,
        val ignoredCalls: Set<CallPredicate>,
        val versionInfo: MemoryVersionInfo,
        override val iteration: Int
) : SolverQuery<CallResolveSolverQuery, RecoveredModel> {
    override fun transform(transformer: (PredicateState) -> PredicateState) =
            CallResolveSolverQuery(transformer(state), transformer(positivePath), transformer(negativePath), arguments, ignoredCalls, versionInfo, iteration)

    override fun updateIgnoredCalls(transformer: (Set<CallPredicate>) -> Set<CallPredicate>) =
            CallResolveSolverQuery(state, positivePath, negativePath, arguments, transformer(ignoredCalls), versionInfo, iteration)

    override fun acceptMemoryCorrector(corrector: (PredicateState, MemoryVersionInfo) -> Pair<PredicateState, MemoryVersionInfo>): CallResolveSolverQuery {
        val (newState, newVersionInfo) = corrector(state, versionInfo)
        return CallResolveSolverQuery(newState, positivePath, negativePath, arguments, ignoredCalls, newVersionInfo, iteration)
    }

    override fun updateIteration(updater: (Int) -> Int) =
            CallResolveSolverQuery(state, positivePath, negativePath, arguments, ignoredCalls, versionInfo, updater(iteration))

    override fun toString(): String = "Resolve call solver argument:\nState:\n$state\nPositive:\n$positivePath\nNegative:\n$negativePath"

    override fun run(solver: FixpointSolver): RecoveredModel {
        log.debug(this@CallResolveSolverQuery)
        val result = solver.querySingle(
                {
                    it.dumpQuery(this@CallResolveSolverQuery, debug = true)
                    MemoryUtils.verifyVersions(state)
                    query { RefineFixpointSolverQuery(state, positivePath, negativePath, arguments, versionInfo) }
                },
                { ex ->
                    dumpQuery(this@CallResolveSolverQuery)
                    throw IllegalStateException("$ex")
                }
        )
        log.debug(result)
        return result
    }

    fun wrap() = CallResolveSolverQueryWrapper(this)
}

@Serializable
@SerialName("CallResolveSolverQueryWrapper")
data class CallResolveSolverQueryWrapper(val query: CallResolveSolverQuery) : SolverQuery<CallResolveSolverQueryWrapper, List<RecoveredModel>> {
    override val iteration: Int
        get() = query.iteration

    override fun updateIteration(updater: (Int) -> Int) = query.updateIteration(updater).wrap()
    override fun transform(transformer: (PredicateState) -> PredicateState) = query.transform(transformer).wrap()
    override fun updateIgnoredCalls(transformer: (Set<CallPredicate>) -> Set<CallPredicate>) = query.updateIgnoredCalls(transformer).wrap()
    override fun acceptMemoryCorrector(corrector: (PredicateState, MemoryVersionInfo) -> Pair<PredicateState, MemoryVersionInfo>) = query.acceptMemoryCorrector(corrector).wrap()
    override fun run(solver: FixpointSolver) = listOf(query.run(solver))
}

package org.jetbrains.research.kex.asm.analysis.refinements.solver

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kfg.ClassManager

class FixpointSolver(val cm: ClassManager) {
    inline fun query(crossinline query: Z3FixpointSolver.() -> FixpointResult): List<RecoveredModel> = query(query, { result -> result }, { ex -> throw IllegalStateException("Solver error: $ex") })
    inline fun query(crossinline query: Z3FixpointSolver.() -> FixpointResult, crossinline onError: (FixpointResult?) -> List<RecoveredModel>): List<RecoveredModel> = query(query, { result -> result }, onError)
    inline fun querySingle(crossinline query: Z3FixpointSolver.() -> FixpointResult): RecoveredModel = query(query, { result -> result.first() }, { ex -> throw IllegalStateException("Solver error: $ex") })
    inline fun querySingle(crossinline query: Z3FixpointSolver.() -> FixpointResult, crossinline onError: (FixpointResult?) -> RecoveredModel): RecoveredModel = query(query, { result -> result.first() }, onError)

    inline fun <reified T> query(
            crossinline query: Z3FixpointSolver.() -> FixpointResult,
            crossinline onResult: (List<RecoveredModel>) -> T,
            crossinline onError: (FixpointResult?) -> T
    ): T = try {
        when (val result = Z3FixpointSolver(cm.type).query()) {
            is FixpointResult.Sat -> onResult(result.result)
            is FixpointResult.Unknown -> {
                log.error("Unknown: ${result.reason}")
                onError(result)
            }
            is FixpointResult.Unsat -> {
                log.error("Unsat: ${result.core.contentToString()}")
                onError(result)
            }
        }
    } catch (ex: QueryCheckStatus.FixpointQueryException) {
        log.error("Bad fixpoint query: ${ex.status}")
        onError(null)
    }
}
package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel

sealed class FixpointResult {
    data class Unknown(val reason: String) : FixpointResult()
    data class Unsat(val core: Array<BoolExpr>) : FixpointResult()
    data class Sat(val result: List<RecoveredModel>) : FixpointResult()
}

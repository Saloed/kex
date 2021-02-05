package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.smt.z3.fixpoint.query.FixpointSolverQuery
import org.jetbrains.research.kfg.type.TypeFactory

class FixpointCallCtxWithFunctionCalls(
    tf: TypeFactory, solverQuery: FixpointSolverQuery
) : FixpointCallCtx(tf, solverQuery)
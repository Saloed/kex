package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.smt.z3.Z3OptionBuilder
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.FixpointExprFactory
import org.jetbrains.research.kex.smt.z3.fixpoint.query.FixpointSolverQuery
import org.jetbrains.research.kfg.type.TypeFactory

class FixpointCallCtxWithFunctionCalls(
    tf: TypeFactory, solverQuery: FixpointSolverQuery
) : FixpointCallCtx(tf, solverQuery) {
    override fun mkExprFactory() = FixpointExprFactory.builder()
        .withFunctionCallSupport()
        .withDeclarationsTracking(declarationTracker)
        .build()

    override fun mkOptions() = Z3OptionBuilder()
        .fp.engine("spacer")
        .fp.xform.inlineEager(false)
        .fp.xform.inlineLinear(false)
        .fp.spacer.simplifyPob(true)
}
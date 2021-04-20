package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.smt.z3.Z3OptionBuilder
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.FixpointExprFactory
import org.jetbrains.research.kex.smt.z3.fixpoint.query.FixpointSolverQuery
import org.jetbrains.research.kfg.type.TypeFactory

class FixpointCallCtxWithFunctionCalls(
    tf: TypeFactory, solverQuery: FixpointSolverQuery, val enableFunctionCalls: Boolean
) : FixpointCallCtx(tf, solverQuery) {
    override fun mkExprFactory() = FixpointExprFactory.builder()
        .run { if (enableFunctionCalls) withFunctionCallSupport() else normal() }
        .withDeclarationsTracking(declarationTracker)
        .build()

    override fun mkOptions() = Z3OptionBuilder()
        .fp.engine("spacer")
//        .fp.xform.inlineEager(false)
//        .fp.xform.inlineLinear(false)
//        .fp.spacer.simplifyPob(true)
}

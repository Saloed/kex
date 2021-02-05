package org.jetbrains.research.kex.smt.z3.fixpoint.converter

import org.jetbrains.research.kex.smt.z3.Z3EngineContext
import org.jetbrains.research.kex.smt.z3.Z3ExprFactory
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.DeclarationTracker

class FixpointExprFactory private constructor(override val ctx: Z3EngineContext) : Z3ExprFactory() {
    companion object {
        class FixpointExprFactoryBuilder {
            private var ctx: Z3EngineContext? = null

            fun normal(): FixpointExprFactoryBuilder {
                if (ctx != null) error("Context type already selected")
                ctx = Z3EngineContext.normal()
                return this
            }

            fun withFunctionCallSupport(): FixpointExprFactoryBuilder {
                if (ctx != null) error("Context type already selected")
                ctx = Z3EngineContext.withFunctionCallSupport()
                return this
            }

            fun withDeclarationsTracking(tracker: DeclarationTracker): FixpointExprFactoryBuilder {
                if (ctx == null) error("Context type is not selected")
                ctx?.installDeclarationTracker(tracker)
                return this
            }

            fun build(): FixpointExprFactory {
                val engineCtx = ctx ?: error("Context is not set up")
                return FixpointExprFactory(engineCtx)
            }
        }

        fun builder() = FixpointExprFactoryBuilder()
    }
}

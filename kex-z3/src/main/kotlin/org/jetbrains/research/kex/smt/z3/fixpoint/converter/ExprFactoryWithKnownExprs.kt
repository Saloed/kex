package org.jetbrains.research.kex.smt.z3.fixpoint.converter

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.Dynamic_
import org.jetbrains.research.kex.smt.z3.ExprFactory_
import org.jetbrains.research.kex.smt.z3.Z3EngineContext
import org.jetbrains.research.kex.smt.z3.Z3ValueExpr

class ExprFactoryWithKnownExprs(
    override val ctx: Z3EngineContext,
    val varGenerator: (KexType, String) -> Dynamic_?
) : ExprFactory_() {
    override fun getVarByTypeAndName(type: KexType, name: String, fresh: Boolean): Z3ValueExpr =
        varGenerator(type, name) ?: super.getVarByTypeAndName(type, name, fresh)
}

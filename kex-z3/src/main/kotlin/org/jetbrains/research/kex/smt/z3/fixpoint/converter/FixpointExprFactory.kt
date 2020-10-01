package org.jetbrains.research.kex.smt.z3.fixpoint.converter

import com.microsoft.z3.Sort
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.DeclarationTracker

class FixpointExprFactory private constructor(override val ctx: ContextWithIntSortSizeInfo) : Z3ExprFactory() {
    companion object {
        fun original() = FixpointExprFactory(createContext())
        fun withDeclarationsTracking(tracker: DeclarationTracker) = FixpointExprFactory(DeclarationTrackingContext(tracker))
    }
}

open class DeclarationTrackingContext(val tracker: DeclarationTracker) : ContextWithIntSortSizeInfo() {
    override fun mkConst(p0: String?, p1: Sort?) = super.mkConst(p0, p1).apply {
        tracker.add("$this", sort, this)
    }

    override fun mkFreshConst(p0: String?, p1: Sort?) = super.mkFreshConst(p0, p1).apply {
        tracker.add("$this", sort, this)
    }
}
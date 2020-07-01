package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.Sort
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.predicate.CallPredicate

class FixpointExprFactory private constructor(override val ctx: ContextWithIntSortSizeInfo) : Z3ExprFactory() {
    companion object {
        fun original() = FixpointExprFactory(createContext())
        fun withDeclarationsTracking(tracker: DeclarationTracker) = FixpointExprFactory(DeclarationTrackingContext(tracker))
        fun withDeclarationsTrackingAndCallConverter(tracker: DeclarationTracker, converter: CallPredicateConverter) = FixpointExprFactory(ContextWithCallSupport(converter, tracker))
    }
}

open class ContextWithCallSupport(
        val converter: CallPredicateConverter, tracker: DeclarationTracker
) : DeclarationTrackingContext(tracker) {

    fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool =
            this.converter.convert(call, ef, ctx, converter)

}

open class DeclarationTrackingContext(val tracker: DeclarationTracker) : ContextWithIntSortSizeInfo() {

    override fun mkConst(p0: String?, p1: Sort?) = super.mkConst(p0, p1).apply {
        tracker.add("$this", sort, this)
    }

    override fun mkFreshConst(p0: String?, p1: Sort?) = super.mkFreshConst(p0, p1).apply {
        tracker.add("$this", sort, this)
    }

}

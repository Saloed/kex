package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.Context
import com.microsoft.z3.Sort
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.DeclarationTracker


open class Z3EngineContext : Context {
    constructor() : super()
    private constructor(params: Map<String, String>) : super(params)

    val intSortSize = hashMapOf<Int, Int>()
    private var declarationTracker: DeclarationTracker? = null

    fun installDeclarationTracker(tracker: DeclarationTracker) {
        if (declarationTracker != null) error("Trying to install more then one declaration tracker")
        declarationTracker = tracker
    }

    override fun mkConst(p0: String?, p1: Sort?) = super.mkConst(p0, p1).apply {
        declarationTracker?.add("$this", sort, this)
    }

    override fun mkFreshConst(p0: String?, p1: Sort?) = super.mkFreshConst(p0, p1).apply {
        declarationTracker?.add("$this", sort, this)
    }

    companion object {
        fun normal() = Z3EngineContext()
        fun withFunctionCallSupport() = Z3EngineContext(mapOf("enable_function_call_support" to "true"))
    }
}

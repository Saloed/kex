package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.Expr
import com.microsoft.z3.Sort

class DeclarationTracker {
    val declarations = hashSetOf<Declaration>()

    data class Declaration(val name: String, val sort: Sort, val expr: Expr) {
        val isArg: Boolean by lazy { name.startsWith("arg$") }
        val isMemory: Boolean by lazy { name.matches(Regex("__memory__\\d+")) }
    }

    fun add(name: String, sort: Sort, expr: Expr) {
        declarations.add(Declaration(name, sort, expr))
    }

}

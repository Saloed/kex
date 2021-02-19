package org.jetbrains.research.kex.smt.z3.fixpoint.query.recursion

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.SolverExpr_
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.smt.z3.fixpoint.model.TermDependency
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.Term

class ExternalCallDeclarationMapping(
    declarationMapping: ModelDeclarationMapping,
    val argMapping: ExternalCallArgMapping,
    val callIndex: Int,
    val callPredicate: CallPredicate
) : ModelDeclarationMapping(declarationMapping.arguments) {
    init {
        terms.putAll(declarationMapping.terms)
        callDependentDeclarations.putAll(declarationMapping.callDependentDeclarations)
        calls.putAll(declarationMapping.calls)
    }

    override fun getConst(expr: SolverExpr_, type: KexType, callDependencies: MutableSet<TermDependency>): Term {
        val term = argMapping.termMap[expr.id] ?: argMapping.mapVar(expr, type)
        if (term == argMapping.result) {
            callDependencies.add(TermDependency.CallResultDependency(term, callIndex, callPredicate))
        }
        return term
    }

}

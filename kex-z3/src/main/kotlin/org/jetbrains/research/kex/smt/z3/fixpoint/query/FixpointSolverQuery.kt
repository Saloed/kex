package org.jetbrains.research.kex.smt.z3.fixpoint.query

import org.jetbrains.research.kex.smt.z3.Z3Converter
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kfg.type.TypeFactory

abstract class FixpointSolverQuery {
    open fun makeConverter(tf: TypeFactory) = Z3Converter(tf)
    abstract fun allStatesForMemoryInitialization(): List<PredicateState>
    abstract fun makeQuery(ctx: Z3FixpointSolver.CallCtx): FixpointSolverCall
    open val Z3FixpointSolver.CallCtx.psConverter: Z3Converter
        get() = converter
}

data class FixpointSolverCall(
        val predicates: List<Z3FixpointSolver.Predicate>,
        val mapper: ModelDeclarationMapping,
        val statementBuilder: StatementBuilder
)

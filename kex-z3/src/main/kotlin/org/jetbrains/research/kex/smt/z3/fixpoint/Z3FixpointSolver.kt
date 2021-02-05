package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations
import org.jetbrains.research.kex.smt.z3.fixpoint.query.FixpointSolverQuery
import org.jetbrains.research.kfg.type.TypeFactory

class Z3FixpointSolver(val tf: TypeFactory) {

    data class Predicate(val idx: Int) {
        val name = "$BASE_NAME$idx"
        fun call(ctx: FixpointCallCtx, arguments: ArgumentDeclarations) = ctx.build {
            val argumentsSorts = arguments.declarations.map { it.sort }
            val callArguments = arguments.declarations.map { it.expr }
            val predicate = ctx.boolFunction(name, argumentsSorts)
            boolFunctionApp(predicate, callArguments)
        }

        companion object {
            const val BASE_NAME = "function_argument_predicate__"
            val idxRegex = Regex("$BASE_NAME(\\d+)")
            fun getPredicateIdx(name: String): Int {
                return idxRegex.find(name)?.groupValues?.get(1)?.toInt()
                    ?: throw IllegalStateException("No predicate idx")
            }
        }
    }

    fun query(builder: () -> FixpointSolverQuery): FixpointResult {
        val query = builder()
        return query.mkContext(tf).use {
            val call = query.makeQuery(it)
            it.callSolver(call.predicates, call.mapper, call.statementBuilder)
        }
    }
}

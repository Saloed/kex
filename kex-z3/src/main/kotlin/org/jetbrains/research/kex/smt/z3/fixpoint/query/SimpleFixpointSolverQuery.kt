package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.smt.z3.fixpoint.UnknownCallsProcessor
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo

class SimpleFixpointSolverQuery(
        val state: PredicateState,
        val positivePaths: List<PredicateState>,
        val query: PredicateState,
        val memoryVersionInfo: MemoryVersionInfo
) : FixpointSolverQuery() {
    override fun allStatesForMemoryInitialization() = listOf(state, query) + positivePaths
    override fun makeQuery(ctx: Z3FixpointSolver.CallCtx): FixpointSolverCall {
        val unknownCallsProcessor = UnknownCallsProcessor() + state + positivePaths + query
        val state = unknownCallsProcessor.apply(state)
        val positivePaths = unknownCallsProcessor.apply(positivePaths)
        val query = unknownCallsProcessor.apply(query)

        val z3State = ctx.build {
            convert(state).asAxiom() as BoolExpr
        }
        val z3positive = positivePaths.map { ctx.convert(it).asAxiom() as BoolExpr }
        val z3query = ctx.convert(query).asAxiom() as BoolExpr

        log.debug("State:\n$z3State\nPositive:\n$z3positive\nQuery:\n$z3query")

        val declarationExprs = ctx.knownDeclarations.map { it.expr }
        val argumentDeclarations = ArgumentDeclarations.create(ctx.knownDeclarations.filter { it.isValuable() })
        val declarationMapping = ModelDeclarationMapping.create(
                argumentDeclarations, memoryVersionInfo,
                state, query, *positivePaths.toTypedArray()
        )
        unknownCallsProcessor.addToDeclarationMapping(declarationMapping)

        val predicates = z3positive.indices.map { idx -> Z3FixpointSolver.Predicate(idx) }

        return FixpointSolverCall(predicates, declarationMapping, object : StatementBuilder(ctx, z3State, declarationExprs) {
            override fun StatementOperation.positiveStatement() = z3positive.mapIndexed { idx, it ->
                ctx.build {
                    val statement = (getState() and it) implies applyPredicate(predicates[idx], argumentDeclarations)
                    statement.forall(declarations).typedSimplify()
                }
            }

            override fun StatementOperation.queryStatement() = ctx.build {
                val predicateApplications = predicates.map { applyPredicate(it, argumentDeclarations) }
                val applications = predicateApplications.toTypedArray()
                val allApplications = context.mkOr(*applications)
                val statement = ((getState() and z3query) and allApplications) implies context.mkFalse()
                statement.forall(declarations).typedSimplify()
            }
        })
    }

}

package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithCallMemory
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.state.BasicState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kfg.type.TypeFactory

class RefineFixpointSolverQuery (
        val state: PredicateState,
        val positive: PredicateState,
        val negative: PredicateState,
        val additionalArgs: List<Term>,
        val memoryInfo: MemoryVersionInfo
): FixpointSolverQuery(){
    override fun makeConverter(tf: TypeFactory) = Z3ConverterWithCallMemory(tf, memoryInfo)
    override fun allStatesForMemoryInitialization() = listOf(state, positive, negative)
    override val Z3FixpointSolver.CallCtx.psConverter: Z3ConverterWithCallMemory
        get() = converter as Z3ConverterWithCallMemory

    override fun makeQuery(ctx: Z3FixpointSolver.CallCtx): FixpointSolverCall {
        val z3State = ctx.build {
            convert(state).asAxiom() as BoolExpr
        }
        val z3positive = ctx.convert(positive).asAxiom() as BoolExpr
        val z3query = ctx.convert(negative).asAxiom() as BoolExpr

        val additionalArgsDeclarations = additionalArgs.map { term ->
            val expr = ctx.converter.convert(term, ctx.ef, ctx.z3Context).expr
            val declaration = ctx.knownDeclarations.first { it.expr == expr }
            term to declaration
        }.toMap()
        val argumentDeclarations = ArgumentDeclarations.create((ctx.knownDeclarations.filter { it.isValuable() } + additionalArgsDeclarations.values).distinct())
        val declarationExprs = (ctx.knownDeclarations.map { it.expr } + additionalArgsDeclarations.values.map { it.expr }).distinct()
        val declarationMapping = ModelDeclarationMapping.create(
                argumentDeclarations, memoryInfo,
                state, positive, negative,
                BasicState(additionalArgs.map { EqualityPredicate(it, it) })
        )
        additionalArgsDeclarations.forEach { (term, decl) -> declarationMapping.setTerm(decl, term) }
        declarationMapping.initializeCalls(ctx.psConverter.getCallsInfo())

        val predicate = Z3FixpointSolver.Predicate(0)

        return FixpointSolverCall(listOf(predicate), declarationMapping, object : StatementBuilder(z3State, declarationExprs) {
            override fun StatementOperation.positiveStatement(): List<BoolExpr> {
                val statement = ctx.build {
                    val statement = (getState() and z3positive) implies applyPredicate(ctx, predicate, argumentDeclarations)
                    statement.forall(declarationExprs).typedSimplify()
                }
                return listOf(statement)
            }

            override fun StatementOperation.queryStatement() = ctx.build {
                val statement = (getState() and z3query and applyPredicate(ctx, predicate, argumentDeclarations)) implies context.mkFalse()
                statement.forall(declarationExprs).typedSimplify()
            }
        })
    }

}

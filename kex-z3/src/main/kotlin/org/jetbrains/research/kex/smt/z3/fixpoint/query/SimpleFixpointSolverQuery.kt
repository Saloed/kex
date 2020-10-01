package org.jetbrains.research.kex.smt.z3.fixpoint.query

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithCallMemory
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.Declaration
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kfg.type.TypeFactory

class SimpleFixpointSolverQuery(
        val state: PredicateState,
        val positivePaths: List<PredicateState>,
        val query: PredicateState,
        val ignoredCalls: Set<CallPredicate>,
        val memoryVersionInfo: MemoryVersionInfo
) : FixpointSolverQuery() {
    override val Z3FixpointSolver.CallCtx.psConverter: Z3ConverterWithCallMemory
        get() = converter as Z3ConverterWithCallMemory

    override fun makeConverter(tf: TypeFactory) = Z3ConverterWithCallMemory(tf, memoryVersionInfo)
    override fun allStatesForMemoryInitialization() = listOf(state, query) + positivePaths
    override fun makeQuery(ctx: Z3FixpointSolver.CallCtx): FixpointSolverCall {
        val z3State = ctx.build {
            convert(state).asAxiom() as BoolExpr
        }
        val z3positive = positivePaths.map { ctx.convert(it).asAxiom() as BoolExpr }
        val z3query = ctx.convert(query).asAxiom() as BoolExpr

        val calls = ctx.psConverter.getCallsInfo()
        val ignoredCallIds = ignoredCalls.mapNotNull { ctx.psConverter.callInfo[it] }.map { it.index }.toSet()
        val ignoredCallsMemoryVersions = ignoredCalls.map { it.memoryVersion }.toSet()
        val declarationExprs = ctx.knownDeclarations.map { it.expr }
        val argumentDeclarations = ctx.knownDeclarations
                .filter { it.isValuable() }
                .filterNot { it is Declaration.CallResult && it.index in ignoredCallIds }
                .filterNot { it is Declaration.Memory && it.version in ignoredCallsMemoryVersions }
                .let { ArgumentDeclarations.create(it) }
        val declarationMapping = ModelDeclarationMapping.create(
                argumentDeclarations, memoryVersionInfo,
                state, query, *positivePaths.toTypedArray()
        )
        declarationMapping.initializeCalls(calls)

        log.debug("$argumentDeclarations")

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

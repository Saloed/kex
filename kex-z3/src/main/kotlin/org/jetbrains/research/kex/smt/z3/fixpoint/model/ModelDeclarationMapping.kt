package org.jetbrains.research.kex.smt.z3.fixpoint.model

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.SolverExpr_
import org.jetbrains.research.kex.smt.z3.fixpoint.converter.Z3ConverterWithCallMemory
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.Declaration
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.term.ArgumentTerm
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.ValueTerm
import org.jetbrains.research.kex.state.transformer.collectArguments

open class ModelDeclarationMapping(val arguments: ArgumentDeclarations) {
    val terms = hashMapOf<Declaration, Term>()
    val callDependentDeclarations =
        hashMapOf<Pair<MemoryDescriptor, MemoryVersion>, Z3ConverterWithCallMemory.CallInfo>()
    val calls = hashMapOf<Int, Z3ConverterWithCallMemory.CallInfo>()

    fun initializeTerms(vararg ps: PredicateState) {
        val (thisArg, otherArgs) = collectArguments(ps)
        arguments.declarations.filterIsInstance<Declaration.This>().forEach { declaration ->
            terms[declaration] = thisArg
                ?: throw IllegalStateException("This $declaration not found ")
        }
        arguments.declarations.filterIsInstance<Declaration.Argument>().forEach { declaration ->
            terms[declaration] = otherArgs.values.find { it.index == declaration.index }
                ?: throw IllegalStateException("Argument $declaration not found ")
        }
    }

    fun initializeCalls(calls: List<Z3ConverterWithCallMemory.CallInfo>) {
        calls.associateByTo(this.calls) { it.index }
        initializeCallDependentMemory(calls)
    }

    private fun initializeCallDependentMemory(calls: List<Z3ConverterWithCallMemory.CallInfo>) {
        val callMemoryVersions = calls.associateBy { it.predicate.memoryVersion }
        arguments.declarations.filterIsInstance<Declaration.Memory>()
            .map { it to callMemoryVersions[it.version] }
            .filter { it.second != null }
            .associateByTo(callDependentDeclarations, { it.first.descriptor to it.first.version }, { it.second!! })
    }

    fun setTerm(declaration: Declaration, term: Term) {
        terms[declaration] = term
    }

    fun getTerm(idx: Int, callDependencies: MutableSet<TermDependency>): Term {
        val declaration = arguments[idx]
        if (declaration is Declaration.CallResult) {
            val callInfo = calls[declaration.index]
                ?: error("No info about call $declaration")
            val term = callInfo.predicate.lhv
            callDependencies.add(TermDependency.CallResultDependency(term, callInfo.index, callInfo.predicate))
            return term
        }
        val term = terms[declaration]
            ?: error("No term for declaration $idx: ${arguments[idx]}")
        if (term is CallTerm) error("Unexpected CallTerm")
        return term
    }

    fun getMemory(idx: Int) = arguments[idx] as? Declaration.Memory
        ?: error("Non memory descriptor")

    open fun getConst(expr: SolverExpr_, type: KexType, callDependencies: MutableSet<TermDependency>): Term {
        error("Unsupported operation")
    }

    open fun getConstMemory(expr: SolverExpr_): Declaration.Memory {
        error("Unsupported operation")
    }

    private fun collectArguments(ps: Array<out PredicateState>): Pair<ValueTerm?, Map<Int, ArgumentTerm>> {
        val collected = ps.map { collectArguments(it) }
        val thisArg = collected.mapNotNull { it.first }.firstOrNull()
        val args = collected.map { it.second }
            .reduce { acc: Map<Int, ArgumentTerm>, current: Map<Int, ArgumentTerm> -> acc + current }
        return thisArg to args
    }

    override fun toString(): String = "ModelDeclarationMappings($arguments)"

    companion object {
        fun create(
            arguments: ArgumentDeclarations,
            memoryVersionInfo: MemoryVersionInfo,
            vararg ps: PredicateState
        ): ModelDeclarationMapping {
            val argumentsWithMemory = arguments.initializeMemoryVersions(memoryVersionInfo)
            return ModelDeclarationMapping(argumentsWithMemory)
                .apply { initializeTerms(*ps) }
        }
    }
}

package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.term.ArgumentTerm
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.ValueTerm
import org.jetbrains.research.kex.state.transformer.collectArguments

class ModelDeclarationMapping(val declarations: MutableList<Declaration>) {
    private val terms = hashMapOf<Declaration, Term>()
    val callDependentDeclarations = hashMapOf<Pair<MemoryDescriptor, MemoryVersion>, Z3ConverterWithCallMemory.CallInfo>()
    val calls = hashMapOf<Int, Z3ConverterWithCallMemory.CallInfo>()


    fun initializeTerms(vararg ps: PredicateState) {
        val (thisArg, otherArgs) = collectArguments(ps)
        declarations.filterIsInstance<Declaration.This>().forEach { declaration ->
            terms[declaration] = thisArg
                    ?: throw IllegalStateException("This $declaration not found ")
        }
        declarations.filterIsInstance<Declaration.Argument>().forEach { declaration ->
            terms[declaration] = otherArgs.values.find { it.index == declaration.index }
                    ?: throw IllegalStateException("Argument $declaration not found ")
        }
    }

    fun initializeCalls(calls: List<Z3ConverterWithCallMemory.CallInfo>) {
        calls.associateByTo(this.calls) { it.index }
        initializeCallDependentMemory(calls)
    }

    fun initializeMemoryVersions(memoryVersionInfo: MemoryVersionInfo) = declarations.replaceAll { declaration ->
        when (declaration) {
            is Declaration.Memory -> {
                val originalVersion = memoryVersionInfo.findMemoryVersion(declaration.descriptor, declaration.version)
                        ?: error("No such memory info $declaration")
                Declaration.Memory(declaration.descriptor, originalVersion, declaration.info)
            }
            else -> declaration
        }
    }

    private fun initializeCallDependentMemory(calls: List<Z3ConverterWithCallMemory.CallInfo>) {
        val callMemoryVersions = calls.associateBy { it.predicate.memoryVersion }
        declarations.filterIsInstance<Declaration.Memory>()
                .map { it to callMemoryVersions[it.version] }
                .filter { it.second != null }
                .associateByTo(callDependentDeclarations, { it.first.descriptor to it.first.version }, { it.second!! })
    }

    fun setTerm(declaration: Declaration, term: Term) {
        terms[declaration] = term
    }

    fun getTerm(idx: Int, callDependencies: MutableSet<TermDependency>): TermWithAxiom {
        val declaration = declarations[idx]
        if (declaration is Declaration.CallResult) {
            val callInfo = calls[declaration.index] ?: throw IllegalStateException("No info about call $declaration")
            val term = callInfo.predicate.lhv
            callDependencies.add(TermDependency.CallResultDependency(term, callInfo.index, callInfo.predicate))
            return TermWithAxiom(term)
        }
        val term = terms[declaration]
                ?: throw IllegalArgumentException("No term for declaration $idx: ${declarations[idx]}")
        if (term is CallTerm) throw IllegalStateException("Unexpected CallTerm")
        return TermWithAxiom(term)
    }


    private fun collectArguments(ps: Array<out PredicateState>): Pair<ValueTerm?, Map<Int, ArgumentTerm>> {
        val collected = ps.map { collectArguments(it) }
        val thisArg = collected.mapNotNull { it.first }.firstOrNull()
        val args = collected.map { it.second }.reduce { acc: Map<Int, ArgumentTerm>, current: Map<Int, ArgumentTerm> -> acc + current }
        return thisArg to args
    }

    override fun toString(): String = "ModelDeclarationMappings($declarations)"

    companion object {
        fun create(declarations: List<Declaration>, memoryVersionInfo: MemoryVersionInfo, vararg ps: PredicateState): ModelDeclarationMapping {
            val mapping = ModelDeclarationMapping(declarations.toMutableList())
            mapping.initializeTerms(*ps)
            mapping.initializeMemoryVersions(memoryVersionInfo)
            return mapping
        }
    }
}

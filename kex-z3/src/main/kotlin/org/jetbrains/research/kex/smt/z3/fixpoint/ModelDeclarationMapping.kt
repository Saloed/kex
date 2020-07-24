package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.collectArguments
import org.jetbrains.research.kex.state.transformer.collectPointers
import org.jetbrains.research.kex.state.transformer.memspace

class ModelDeclarationMapping(val declarations: List<DeclarationTracker.Declaration>) {
    private val terms = hashMapOf<DeclarationTracker.Declaration, Term>()
    private val arrayMemories = mutableSetOf<DeclarationTracker.Declaration>()
    val calls = hashMapOf<Int, Z3ContextWithCallMemory.CallInfo>()

    fun initializeTerms(vararg ps: PredicateState) {
        val (thisArg, otherArgs) = collectArguments(ps)
        declarations.filterIsInstance<DeclarationTracker.Declaration.This>().forEach { declaration ->
            terms[declaration] = thisArg
                    ?: throw IllegalStateException("This $declaration not found ")
        }
        declarations.filterIsInstance<DeclarationTracker.Declaration.Argument>().forEach { declaration ->
            terms[declaration] = otherArgs.values.find { it.index == declaration.index }
                    ?: throw IllegalStateException("Argument $declaration not found ")
        }
    }

    fun initializeArrays(vararg ps: PredicateState) {
        val memories = declarations.filterIsInstance<DeclarationTracker.Declaration.Memory>()
        if (memories.isEmpty()) return
        val pointers = ps.map { collectPointers(it) }.reduce { acc: Set<Term>, curr: Set<Term> -> acc + curr }
        val memoryPointers = memories.map { mem -> pointers.filter { it.memspace == mem.memspace } }
        val memoriesUnderArray = memoryPointers.zip(memories).filter { it.first.all { it is ArrayIndexTerm } }.map { it.second }
        arrayMemories.addAll(memoriesUnderArray)
    }

    fun initializeCalls(calls: List<Z3ContextWithCallMemory.CallInfo>) {
        calls.map { it.index to it }.toMap(this.calls)
    }

    fun setTerm(declaration: DeclarationTracker.Declaration, term: Term) {
        terms[declaration] = term
    }

    fun getTerm(idx: Int, callDependencies: MutableSet<TermDependency>): TermWithAxiom {
        val declaration = declarations[idx]
        if (declaration is DeclarationTracker.Declaration.Call) {
            val callInfo = calls[declaration.index] ?: throw IllegalStateException("No info about call $declaration")
            if (declaration is DeclarationTracker.Declaration.Call.CallResult) {
                val term = callInfo.predicate.lhv
                callDependencies.add(TermDependency(term, callInfo.predicate, DependencyType.RETURN_VALUE))
                return TermWithAxiom(term)
            }
            TODO("Term for unknown call")
        }
        val term = terms[declaration]
                ?: throw IllegalArgumentException("No term for declaration $idx: ${declarations[idx]}")
        if (term is CallTerm) throw IllegalStateException("Unexpected CallTerm")
        return TermWithAxiom(term)
    }

    fun isArrayMemory(declaration: DeclarationTracker.Declaration) = declaration in arrayMemories

    private fun collectArguments(ps: Array<out PredicateState>): Pair<ValueTerm?, Map<Int, ArgumentTerm>> {
        val collected = ps.map { collectArguments(it) }
        val thisArg = collected.mapNotNull { it.first }.firstOrNull()
        val args = collected.map { it.second }.reduce { acc: Map<Int, ArgumentTerm>, current: Map<Int, ArgumentTerm> -> acc + current }
        return thisArg to args
    }

    override fun toString(): String = "ModelDeclarationMappings($declarations)"

    companion object {
        fun create(declarations: List<DeclarationTracker.Declaration>, vararg ps: PredicateState): ModelDeclarationMapping {
            val mapping = ModelDeclarationMapping(declarations)
            mapping.initializeTerms(*ps)
            mapping.initializeArrays(*ps)
            return mapping
        }
    }
}

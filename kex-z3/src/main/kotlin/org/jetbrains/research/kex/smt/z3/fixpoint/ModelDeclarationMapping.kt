package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.term.ArrayIndexTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.collectArguments
import org.jetbrains.research.kex.state.transformer.collectPointers
import org.jetbrains.research.kex.state.transformer.memspace

class ModelDeclarationMapping(val declarations: List<DeclarationTracker.Declaration>) {
    private val terms = declarations.map { null }.toMutableList<Term?>()
    private val arrayMemories = mutableSetOf<DeclarationTracker.Declaration>()

    fun initializeTerms(ps: PredicateState) {
        val (thisArg, otherArgs) = collectArguments(ps)
        for ((index, declaration) in declarations.withIndex()) {
            if (declaration !is DeclarationTracker.Declaration.Argument) continue
            val term = otherArgs.values.find { it.index == declaration.index }
                    ?: throw IllegalStateException("Argument $declaration not found ")
            terms[index] = term
        }
    }

    fun initializeArrays(ps: PredicateState) {
        val memories = declarations.filterIsInstance<DeclarationTracker.Declaration.Memory>()
        if (memories.isEmpty()) return
        val pointers = collectPointers(ps)
        val memoryPointers = memories.map { mem -> pointers.filter { it.memspace == mem.memspace } }
        val memoriesUnderArray = memoryPointers.zip(memories).filter { it.first.all { it is ArrayIndexTerm } }.map { it.second }
        arrayMemories.addAll(memoriesUnderArray)
    }

    fun setTerm(declaration: DeclarationTracker.Declaration, term: Term) {
        val idx = declarations.indexOf(declaration)
        if (idx == -1) throw IllegalArgumentException("Unknown declaration: $declaration")
        terms[idx] = term
    }

    fun getTerm(idx: Int): Term = terms[idx]
            ?: throw IllegalArgumentException("No term for declaration $idx: ${declarations[idx]}")

    fun isArrayMemory(declaration: DeclarationTracker.Declaration) = declaration in arrayMemories

    companion object {
        fun create(declarations: List<DeclarationTracker.Declaration>, ps: PredicateState): ModelDeclarationMapping {
            val mapping = ModelDeclarationMapping(declarations)
            mapping.initializeTerms(ps)
            mapping.initializeArrays(ps)
            return mapping
        }
    }
}

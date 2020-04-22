package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.term.ArgumentTerm
import org.jetbrains.research.kex.state.term.ArrayIndexTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.ValueTerm
import org.jetbrains.research.kex.state.transformer.collectArguments
import org.jetbrains.research.kex.state.transformer.collectPointers
import org.jetbrains.research.kex.state.transformer.memspace
import org.jetbrains.research.kex.util.join

class ModelDeclarationMapping(val declarations: List<DeclarationTracker.Declaration>) {
    private val terms = hashMapOf<DeclarationTracker.Declaration, Term>()
    private val arrayMemories = mutableSetOf<DeclarationTracker.Declaration>()

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
        val pointers = ps.map { collectPointers(it) }.join { acc, curr -> acc + curr }
        val memoryPointers = memories.map { mem -> pointers.filter { it.memspace == mem.memspace } }
        val memoriesUnderArray = memoryPointers.zip(memories).filter { it.first.all { it is ArrayIndexTerm } }.map { it.second }
        arrayMemories.addAll(memoriesUnderArray)
    }

    fun setTerm(declaration: DeclarationTracker.Declaration, term: Term) {
        terms[declaration] = term
    }

    fun getTerm(idx: Int): Term = terms[declarations[idx]]
            ?: throw IllegalArgumentException("No term for declaration $idx: ${declarations[idx]}")

    fun isArrayMemory(declaration: DeclarationTracker.Declaration) = declaration in arrayMemories

    private fun collectArguments(ps: Array<out PredicateState>): Pair<ValueTerm?, Map<Int, ArgumentTerm>> {
        val collected = ps.map { collectArguments(it) }
        val thisArg = collected.mapNotNull { it.first }.firstOrNull()
        val args = collected.map { it.second }.join { acc, current -> acc + current }
        return thisArg to args
    }

    companion object {
        fun create(declarations: List<DeclarationTracker.Declaration>, vararg ps: PredicateState): ModelDeclarationMapping {
            val mapping = ModelDeclarationMapping(declarations)
            mapping.initializeTerms(*ps)
            mapping.initializeArrays(*ps)
            return mapping
        }
    }
}

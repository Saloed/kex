package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.smt.z3.VersionedMemory
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.ArrayStorePredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.ArrayLoadTerm
import org.jetbrains.research.kex.state.term.FieldTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace

class ContextMemoryInitializer(vararg states: PredicateState) {
    private val initializationStates = states
    fun apply(context: Z3Context) {
        val initializer = MemoryInitializer(context)
        for (state in initializationStates) {
            initializer.apply(state)
        }
    }

    private class MemoryInitializer(val ctx: Z3Context) : Transformer<MemoryInitializer> {
        override fun transformFieldTerm(term: FieldTerm): Term {
            initializePropertyMemory(term.memspace, "${term.klass}.${term.fieldNameString}")
            return super.transformFieldTerm(term)
        }

        override fun transformArrayStore(predicate: ArrayStorePredicate): Predicate {
            initializeArrayMemory(predicate.arrayRef.memspace)
            return super.transformArrayStore(predicate)
        }

        override fun transformArrayLoad(term: ArrayLoadTerm): Term {
            initializeArrayMemory(term.arrayRef.memspace)
            return super.transformArrayLoad(term)
        }

        private fun initializeArrayMemory(memspace: Int) {
            val memoryName = Z3Context.memoryName(memspace)
            val memory = emptyMemory(memoryName)
            ctx.setMemory(memspace, memory)
        }

        private fun initializePropertyMemory(memspace: Int, name: String) {
            val propertyName = Z3Context.propertyName(memspace, name)
            val memory = emptyMemory(propertyName)
            ctx.setProperties(memspace, name, memory)
        }

        private fun emptyMemory(name: String) = VersionedMemory(ctx.factory.makeEmptyMemory(name))
    }
}

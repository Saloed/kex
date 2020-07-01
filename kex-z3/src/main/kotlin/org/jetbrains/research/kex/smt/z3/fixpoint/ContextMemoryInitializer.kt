package org.jetbrains.research.kex.smt.z3.fixpoint

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
            val memspace = term.memspace
            val name = term.fieldNameString
            val klass = term.klass
            ctx.getProperties(memspace, "${klass}.${name}")
            return super.transformFieldTerm(term)
        }

        override fun transformArrayStore(predicate: ArrayStorePredicate): Predicate {
            initializeArrayMemory(predicate.arrayRef)
            return super.transformArrayStore(predicate)
        }

        override fun transformArrayLoad(term: ArrayLoadTerm): Term {
            initializeArrayMemory(term.arrayRef)
            return super.transformArrayLoad(term)
        }

        private fun initializeArrayMemory(array: Term) {
            val memspace = array.memspace
            ctx.getMemory(memspace)
        }
    }
}

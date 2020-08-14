package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.smt.z3.Z3Converter
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.ArrayStorePredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.ArrayLoadTerm
import org.jetbrains.research.kex.state.term.FieldTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.memspace

class ContextMemoryInitializer(vararg states: PredicateState) {
    private val initializationStates = states
    fun apply(context: Z3Context, converter: Z3Converter) {
        val initializer = MemoryInitializer(context, converter)
        for (state in initializationStates) {
            initializer.apply(state)
        }
    }

    private class MemoryInitializer(val ctx: Z3Context, val converter: Z3Converter) : Transformer<MemoryInitializer> {
        override fun transformFieldTerm(term: FieldTerm): Term {
            val type = term { term.load() }.type
            initializePropertyMemory(term.memspace, "${term.klass}.${term.fieldNameString}", type)
            return super.transformFieldTerm(term)
        }

        override fun transformArrayStore(predicate: ArrayStorePredicate): Predicate {
            initializeArrayMemory(predicate.arrayRef.memspace, predicate.componentType)
            return super.transformArrayStore(predicate)
        }

        override fun transformArrayLoad(term: ArrayLoadTerm): Term {
            initializeArrayMemory(term.arrayRef.memspace, term.type)
            return super.transformArrayLoad(term)
        }

        private fun initializeArrayMemory(memspace: Int, type: KexType) {
            val memoryName = Z3Context.memoryName(memspace)
            val memory = emptyMemory(memoryName, type)
            ctx.setMemory(memspace, memory)
        }

        private fun initializePropertyMemory(memspace: Int, name: String, type: KexType) {
            val propertyName = Z3Context.propertyName(memspace, name)
            val memory = emptyMemory(propertyName, type)
            ctx.setProperties(name, memspace, memory)
        }

        private fun emptyMemory(name: String, type: KexType) = ctx.emptyMemory(name, MemoryVersion.initial(), converter.Z3Type(type))
    }
}

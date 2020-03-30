package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.ConstantPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term

class UnknownCallsProcessor(val ignore: Set<CallPredicate> = emptySet()) {
    data class UnknownCall(val idx: Int, val call: CallTerm, val variable: Term)

    private val states = arrayListOf<PredicateState>()
    private val replacement = hashMapOf<CallPredicate, Predicate>()
    private val unknownCalls = hashMapOf<Int, UnknownCall>()
    private var initialized = false

    operator fun plus(ps: PredicateState): UnknownCallsProcessor = apply { states.add(ps) }
    operator fun plus(ps: List<PredicateState>): UnknownCallsProcessor = apply { states.addAll(ps) }

    fun apply(ps: PredicateState): PredicateState {
        ensureReplacement()
        return ps.map {
            when (it) {
                !is CallPredicate -> it
                else -> replacement[it] ?: it
            }
        }
    }

    fun apply(ps: List<PredicateState>) = ps.map { apply(it) }

    fun addToDeclarationMapping(declarationMapping: ModelDeclarationMapping) {
        ensureReplacement()
        val calls = declarationMapping.declarations.filterIsInstance<DeclarationTracker.Declaration.Call>()
        for (call in calls) {
            declarationMapping.setTerm(call, unknownCalls[call.index]!!.call)
        }
    }

    fun hasUnknownCalls() = unknownCalls.isNotEmpty()

    fun unknownCalls(): List<UnknownCall> {
        ensureReplacement()
        return unknownCalls.values.toList()
    }

    private fun collectCalls(ps: PredicateState): Set<CallPredicate> {
        val result = hashSetOf<CallPredicate>()
        ps.map {
            if (it is CallPredicate && it !in ignore) {
                result.add(it)
            }
            it
        }
        return result
    }

    private fun ensureReplacement() {
        if (initialized) return
        val calls = states.fold(emptySet<CallPredicate>()) { acc, state -> acc + collectCalls(state) }
        for ((index, call) in calls.withIndex()) {
            if (!call.hasLhv) {
                replacement[call] = ConstantPredicate(true, call.type, call.location)
                continue
            }
            val callVariable = term { value(call.lhv.type, "call__$index") }
            replacement[call] = EqualityPredicate(call.lhv, callVariable, call.type, call.location)
            unknownCalls[index] = UnknownCall(index, call.call as CallTerm, callVariable)
        }
    }


}
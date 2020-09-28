package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.Declaration
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.ConstantPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.term.*

class UnknownCallsProcessor(val ignore: Set<CallPredicate> = emptySet(), val replaceWithArray: Boolean = false) {
    data class UnknownCall(val idx: Int, val call: CallTerm, val variable: Term)

    private val replacement = hashMapOf<CallPredicate, Predicate>()
    private val unknownCalls = hashMapOf<Int, UnknownCall>()

    operator fun plus(ps: PredicateState): UnknownCallsProcessor = apply { analyzeState(ps) }
    operator fun plus(ps: List<PredicateState>): UnknownCallsProcessor = apply { ps.forEach { analyzeState(it) } }

    fun apply(ps: PredicateState): PredicateState {
        return ps.map {
            when (it) {
                !is CallPredicate -> it
                else -> replacement[it] ?: it
            }
        }
    }

    fun apply(ps: List<PredicateState>) = ps.map { apply(it) }

    fun addToDeclarationMapping(declarationMapping: ModelDeclarationMapping) {
        val calls = declarationMapping.arguments.declarations.filterIsInstance<Declaration.CallResult>()
        for (call in calls) {
            val unknownCall = unknownCalls[call.index]
                    ?: throw IllegalStateException("No call for index ${call.index}")
            declarationMapping.setTerm(call, unknownCall.call)
        }
    }

    fun hasUnknownCalls() = replacement.values.any { it !is ConstantPredicate }

    fun unknownCalls(): List<UnknownCall> = unknownCalls.values.toList()

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

    private fun analyzeState(ps: PredicateState) {
        val calls = collectCalls(ps).filterNot { it in replacement }
        for (call in calls) {
            val index = replacement.size
            val (callReplacement, callVariable) = createReplacement(call, index)
            replacement[call] = callReplacement
            unknownCalls[index] = UnknownCall(index, call.call as CallTerm, callVariable)
        }
    }

    private fun createReplacement(call: CallPredicate, index: Int): Pair<Predicate, Term> {
        val callType = when {
            call.hasLhv -> call.lhv.type
            else -> (call.call as CallTerm).method.returnType.kexType
        }

        if (!this.replaceWithArray) {
            val callVariable = term { value(callType, "call__${index}!") }
            val callReplacement = when {
                call.hasLhv -> EqualityPredicate(call.lhv, callVariable, call.type, call.location)
                else -> ConstantPredicate(true, call.type, call.location)
            }
            return callReplacement to callVariable
        }
        TODO()
    }
}

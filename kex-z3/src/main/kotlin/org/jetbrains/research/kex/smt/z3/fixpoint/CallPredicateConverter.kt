package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.predicate.CallPredicate

class CallPredicateConverter {
    private var callCounter = 0
    fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool = when {
        else -> ef.makeTrue()
    }

    private fun Z3Context.currentMemory() = accessRawMemories().toMap()
    private fun Z3Context.cleanupMemory() {
        val memories = accessRawMemories()
        for ((name, _) in memories) {
            memories[name] = VersionedMemory(factory.makeEmptyMemory("${name}_${callCounter}"))
        }
    }

}

package org.jetbrains.research.kex.state.predicate

import com.abdullin.kthelper.assert.asserted
import kotlinx.serialization.Contextual
import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.Location

@InheritorOf("Predicate")
@Serializable
class CallPredicate(
        val lhvUnsafe: Term?,
        val callTermUnsafe: Term,
        @Required override val type: PredicateType = PredicateType.State(),
        @Required @Contextual override val location: Location = Location()) : Predicate() {

    val hasLhv by lazy { lhvUnsafe != null }
    override val operands by lazy { listOfNotNull(lhvUnsafe, callTermUnsafe) }

    constructor(callTerm: Term, type: PredicateType = PredicateType.State(), location: Location = Location())
            : this(null, callTerm, type, location)

    val lhv: Term
        get() = asserted(hasLhv) { operands[0] }

    val call: Term
        get() = if (hasLhv) operands[1] else operands[0]

    val callTerm: CallTerm
        get() = callTermUnsafe as CallTerm

    val memoryVersion: MemoryVersion
        get() = callTerm.memoryVersion

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate {
        val tlhv = if (hasLhv) t.transform(lhv) else null
        val tcall = t.transform(call)
        return when {
            hasLhv -> when {
                tlhv == lhv && tcall == call -> this
                else -> predicate(type, location) { tlhv!!.call(tcall)}
            }
            else -> when (tcall) {
                call -> this
                else -> predicate(type, location) { call(tcall)}
            }
        }
    }

    override fun print(): String {
        val sb = StringBuilder()
        if (hasLhv) sb.append("$lhv = ")
        sb.append(call)
        return sb.toString()
    }
}

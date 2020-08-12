package org.jetbrains.research.kex.state.term

import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer

@InheritorOf("Term")
@Serializable
class IfTerm(
        override val type: KexType,
        val condition: Term,
        val trueBranch: Term,
        val falseBranch: Term,
        override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term() {
    override val name = "if($condition) then ($trueBranch) else ($falseBranch)"
    override val subterms by lazy { listOf(condition, trueBranch, falseBranch) }

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Term {
        val tCond = t.transform(condition)
        val tTrue = t.transform(trueBranch)
        val tFalse = t.transform(falseBranch)
        return when {
            tCond == condition && tTrue == trueBranch && tFalse == falseBranch -> this
            else -> IfTerm(type, tCond, tTrue, tFalse)
        }
    }
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = IfTerm(type, condition, trueBranch, falseBranch, memoryVersion)
}

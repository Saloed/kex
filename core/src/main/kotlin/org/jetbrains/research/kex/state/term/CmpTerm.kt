package org.jetbrains.research.kex.state.term

import com.abdullin.kthelper.defaultHashCode
import kotlinx.serialization.Contextual
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.InheritorOf
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode

@InheritorOf("Term")
@Serializable
class CmpTerm(
        override val type: KexType,
        @Contextual val opcode: CmpOpcode,
        val lhv: Term,
        val rhv: Term,
        override val memoryVersion: MemoryVersion = MemoryVersion.default()) : Term() {
    override val name = "$lhv $opcode $rhv"
    override val subterms by lazy { listOf(lhv, rhv) }

    override fun <T: Transformer<T>> accept(t: Transformer<T>): Term {
        val tlhv = t.transform(lhv)
        val trhv = t.transform(rhv)
        return when {
            tlhv == lhv && trhv == rhv -> this
            else -> term { tf.getCmp(opcode, tlhv, trhv) }
         }
    }

    override fun hashCode() = defaultHashCode(super.hashCode(), opcode)
    override fun equals(other: Any?): Boolean {
        if (other?.javaClass != this.javaClass) return false
        other as CmpTerm
        return super.equals(other) && this.opcode == other.opcode
    }
    override fun withMemoryVersion(memoryVersion: MemoryVersion): Term = CmpTerm(type, opcode, lhv, rhv, memoryVersion)
}
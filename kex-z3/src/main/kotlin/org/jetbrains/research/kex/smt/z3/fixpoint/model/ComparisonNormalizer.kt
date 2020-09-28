package org.jetbrains.research.kex.smt.z3.fixpoint.model

import org.jetbrains.research.kex.state.term.BinaryTerm
import org.jetbrains.research.kex.state.term.CmpTerm
import org.jetbrains.research.kex.state.term.ConstIntTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.value.instruction.BinaryOpcode

internal class ComparisonNormalizer : Transformer<ComparisonNormalizer> {
    override fun transformCmpTerm(term: CmpTerm): Term = normalize(term) ?: term
    private fun normalize(term: CmpTerm): Term? {
        val rhv = term.rhv as? ConstIntTerm ?: return null
        val lhv = term.lhv as? BinaryTerm ?: return null
        val lhvRhv = lhv.rhv as? BinaryTerm ?: return null
        val lhvRhvLhv = lhvRhv.lhv as? ConstIntTerm ?: return null
        if (lhv.opcode !is BinaryOpcode.Add) return null
        if (lhvRhv.opcode !is BinaryOpcode.Mul) return null
        if (lhvRhvLhv.value != -1) return null
        return when (rhv.value) {
            0 -> CmpTerm(term.type, term.opcode, lhv.lhv, lhvRhv.rhv)
            else -> CmpTerm(term.type, term.opcode, lhv.lhv, org.jetbrains.research.kex.state.term.term { lhvRhv.rhv add rhv })
        }
    }
}

package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.exceptions

import com.abdullin.kthelper.defaultHashCode
import org.jetbrains.research.kex.asm.state.PredicateBuilder
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Location
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst

internal class ThrowPredicate(val inst: ThrowInst) : Predicate() {
    override val type: PredicateType = PredicateType.State()
    override val location: Location = inst.location
    override val operands: List<Term> = emptyList()
    override fun print(): String = "THROW ${inst.hashCode()}"

    override fun <T : Transformer<T>> accept(t: Transformer<T>): Predicate = error("Transformers for throw predicate are not supported")

    override fun equals(other: Any?) = super.equals(other) && inst == (other as ThrowPredicate).inst
    override fun hashCode() = defaultHashCode(super.hashCode(), inst)
}

class PredicateBuilderWithThrows(cm: ClassManager) : PredicateBuilder(cm) {
    override fun visitThrowInst(inst: ThrowInst) {
        predicateMap[inst] = ThrowPredicate(inst)
    }
}

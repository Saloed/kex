package org.jetbrains.research.kex.state.transformer

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.CastPredicate
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.assume
import org.jetbrains.research.kex.state.term.InstanceOfTerm
import org.jetbrains.research.kex.state.term.PrimitiveCastTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kfg.type.TypeFactory

class CastInfoAdapter(val tf: TypeFactory) : RecollectingTransformer<CastInfoAdapter> {
    override val builders = dequeOf(StateBuilder())

    // term -> mapOf(type -> condition)
    val instanceOfInfo = mutableMapOf<Term, MutableMap<KexClass, Term>>()


    override fun transformEquality(predicate: EqualityPredicate): Predicate {
        when (val rhv = predicate.rhv) {
            is InstanceOfTerm -> {
                val checkedType = rhv.checkedType as KexClass
                val checkedKfgClass = checkedType.getKfgClass(tf)
                val operand = rhv.operand
                val instanceOfMap = instanceOfInfo.getOrPut(operand, ::mutableMapOf)

                for ((type, condition) in instanceOfMap) {
                    val kfgClass = type.getKfgClass(tf)
                    if (!(kfgClass.isAncestorOf(checkedKfgClass) || checkedKfgClass.isAncestorOf(kfgClass))) {
                        currentBuilder += assume { (predicate.lhv implies !condition) equality true }
                    }
                }
                instanceOfInfo.getOrPut(operand, ::mutableMapOf)[checkedType] = predicate.lhv
            }
            is PrimitiveCastTerm -> {
                // never class type
            }
        }
        return super.transformEquality(predicate)
    }

    override fun transformCast(predicate: CastPredicate): Predicate {
        val newType = predicate.operandType
        if (newType is KexClass) {
            val newKfgClass = newType.getKfgClass(tf)
            val operand = predicate.operand
            val instanceOfMap = instanceOfInfo.getOrPut(operand, ::mutableMapOf)

            for ((type, condition) in instanceOfMap) {
                val kfgClass = type.getKfgClass(tf)
                if (!(kfgClass.isAncestorOf(newKfgClass) || newKfgClass.isAncestorOf(kfgClass))) {
                    currentBuilder += assume { condition equality false }
                }
            }
        }
        return super.transformCast(predicate)
    }
}
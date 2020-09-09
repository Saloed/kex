package org.jetbrains.research.kex.smt.z3.fixpoint

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.memory.MemoryAccessScope
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode
import org.jetbrains.research.kfg.type.Type
import org.jetbrains.research.kfg.type.TypeFactory

internal object UnknownType : KexType() {
    override val name: String = "Unknown"
    override val bitsize: Int = 0
    override fun getKfgType(types: TypeFactory): Type = throw IllegalStateException("type is unknown")
}


internal class InstanceOfCorrector(private val z3Context: Z3Context, private val tf: TypeFactory) : Transformer<InstanceOfCorrector> {
    private val allPossibleTypes = hashMapOf<Term, Term>()
    override fun transformCmpTerm(term: CmpTerm): Term {
        val instanceOfTerm = term.lhv as? InstanceOfTerm ?: return term
        if (instanceOfTerm.checkedType !is UnknownType) return term
        val typeBound = term.rhv as? ConstIntTerm
                ?: error("Term with unknown type has no bound")
        val baseType = instanceOfTerm.operand.type
        val typeMapping = possibleTypes(baseType)
        if (typeMapping.isEmpty()) {
            error("No type candidates for base type: $baseType")
        }
        updateAllTypesInfo(instanceOfTerm, typeMapping.keys)
        val predicate = term.opcode.predicate()
        val selectedTypeCandidates = typeMapping.filterValues { predicate(it, typeBound.value) }.keys
        if (selectedTypeCandidates.isNotEmpty()) {
            return instanceOfTerms(instanceOfTerm.operand, selectedTypeCandidates, instanceOfTerm.memoryVersion, instanceOfTerm.scopeInfo)
        }
        val negatedTypeCandidates = typeMapping.filterValues { !predicate(it, typeBound.value) }.keys
        val instTerms = instanceOfTerms(instanceOfTerm.operand, negatedTypeCandidates, instanceOfTerm.memoryVersion, instanceOfTerm.scopeInfo)
        return term { instTerms.not() }
    }

    private fun updateAllTypesInfo(term: InstanceOfTerm, types: Set<KexType>) {
        val variable = term.operand
        if (variable in allPossibleTypes) return
        allPossibleTypes[variable] = instanceOfTerms(variable, types, term.memoryVersion, term.scopeInfo)
    }

    override fun apply(ps: PredicateState): PredicateState {
        val result = super.apply(ps)
        if (allPossibleTypes.isEmpty()) return result
        val typeConstraints = basic {
            allPossibleTypes.values.forEach {
                assume { it equality true }
            }
        }
        return ChainState(typeConstraints, result)
    }

    private fun instanceOfTerms(variable: Term, types: Set<KexType>, version: MemoryVersion, scope: MemoryAccessScope) = term {
        types.map { tf.getInstanceOf(it, variable).withMemoryVersion(version).withScopeInfo(scope) as Term }
                .reduceOrNull { acc, it -> acc or it }
                ?: const(false)
    }

    private fun possibleTypes(type: KexType) = z3Context.getTypeMapping().filterKeys { it.isInheritorOfBaseType(type) }

    private fun CmpOpcode.predicate(): (Int, Int) -> Boolean = when (this) {
        is CmpOpcode.Eq -> { a, b -> a == b }
        is CmpOpcode.Neq -> { a, b -> a != b }
        is CmpOpcode.Lt -> { a, b -> a < b }
        is CmpOpcode.Gt -> { a, b -> a > b }
        is CmpOpcode.Le -> { a, b -> a <= b }
        is CmpOpcode.Ge -> { a, b -> a >= b }
        else -> throw IllegalStateException("Unsupported $this")
    }

    private fun KexType.isInheritorOfBaseType(type: KexType): Boolean {
        val myType = getKfgType(tf)
        val baseType = type.getKfgType(tf)
        return myType.isSubtypeOf(baseType)
    }

}

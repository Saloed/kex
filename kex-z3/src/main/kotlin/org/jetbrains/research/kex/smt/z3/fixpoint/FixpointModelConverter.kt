package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import com.microsoft.z3.IntExpr
import com.microsoft.z3.IntNum
import com.microsoft.z3.enumerations.Z3_lbool
import org.jetbrains.research.kex.ktype.KexArray
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.term.ArrayLengthTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.ConstantPropagator
import org.jetbrains.research.kex.state.transformer.Optimizer
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.type.TypeFactory

class FixpointModelConverter(
        private val mapping: ModelDeclarationMapping,
        private val tf: TypeFactory
) {

    fun apply(expr: Expr): PredicateState = expr.simplify()
            .let { convert(it) }
            .let { ConstantPropagator.apply(it) }
            .let { Optimizer().apply(it) }
            .simplify()

    private fun convert(expr: Expr): PredicateState = when (expr) {
        is BoolExpr -> convert(expr)
        else -> basic { state { convertTerm(expr) equality const(true) } }
    }

    private fun convertTerm(expr: Expr): Term = when {
        expr.isVar -> variableTerm(expr)
        expr is BoolExpr -> convertTerm(expr)
        expr is IntExpr -> convertTerm(expr)
        else -> TODO()
    }

    private fun variableTerm(expr: Expr) = mapping.getTerm(expr.index)

    private fun convert(expr: BoolExpr): PredicateState = when {
        expr.isAnd -> expr.args.map { convert(it) }.combine { a, b -> ChainState(a, b) }.simplify()
        expr.isOr -> ChoiceState(expr.args.map { convert(it) }).simplify()
        expr.isNot && expr.numArgs == 1 -> basic {
            val arg = convertTerm(expr.args.first())
            state { arg equality const(false) }
        }
        expr.isEq && expr.numArgs == 2 -> basic {
            val (lhs, rhs) = expr.convertArgs()
            state { lhs equality rhs }
        }
        else -> basic { state { convertTerm(expr) equality const(true) } }
    }


    private fun convertTerm(expr: BoolExpr): Term = when {
        expr.isAnd -> term { expr.convertArgs().combine { a, b -> a and b } }
        expr.isOr -> term { expr.convertArgs().combine { a, b -> a or b } }
        expr.isNot && expr.numArgs == 1 -> term { expr.convertArgs().first().not() }
        expr.isEq && expr.numArgs == 2 -> term { expr.convertArgs().combine { a, b -> a eq b } }
        expr.isLE && expr.numArgs == 2 -> term { expr.convertArgs().combine { a, b -> a le b } }
        expr.isGE && expr.numArgs == 2 -> term { expr.convertArgs().combine { a, b -> a ge b } }
        expr.isConst && expr.boolValue == Z3_lbool.Z3_L_TRUE -> term { const(true) }
        expr.isConst && expr.boolValue == Z3_lbool.Z3_L_FALSE -> term { const(false) }
        else -> TODO()
    }

    private fun convertTerm(expr: IntExpr): Term = when {
        expr.isIntNum -> term { const((expr as IntNum).int) }
        expr.isAdd -> term { expr.convertArgs().combine { a, b -> a add b } }
        expr.isMul -> term { expr.convertArgs().combine { a, b -> a mul b } }
        expr.isSelect && expr.numArgs == 2 -> convertMemoryLoad(expr.args[0], expr.args[1])
        else -> TODO()
    }

    private fun convertMemoryLoad(memory: Expr, location: Expr): Term {
        if (!memory.isVar) throw IllegalStateException("Memory is not var $memory")
        val decl = mapping.declarations[memory.index]
        return when {
            decl is DeclarationTracker.Declaration.Property -> when {
                location.isVar -> {
                    val locationVariable = variableTerm(location)
                    readProperty(locationVariable, decl)
                }
                else -> TODO("Property location is not var")
            }
            decl is DeclarationTracker.Declaration.Memory && mapping.isArrayMemory(decl) -> {
                if (!(location.isAdd && location.args.size == 2)) {
                    throw IllegalStateException("Unexpected array memory location $location")
                }
                val (lhs, rhs) = location.convertArgs()
                val (base, index) = when {
                    lhs.type is KexArray -> lhs to rhs
                    rhs.type is KexArray -> rhs to lhs
                    else -> throw IllegalStateException("Array load has no base and index")
                }
                val arrayIndex = term { tf.getArrayIndex(base, index) }
                term { tf.getArrayLoad(arrayIndex) }
            }
            else -> throw IllegalStateException("Unexpected memory $memory : $decl")
        }
    }

    private fun readProperty(obj: Term, property: DeclarationTracker.Declaration.Property): Term = when (property) {
        is DeclarationTracker.Declaration.ClassProperty -> {
            val kType = obj.type.getKfgType(tf)
            if (kType !is ClassType) {
                TODO("Only class types supported")
            }
            val kfgClass = kType.`class`
            if (kfgClass.name != property.className) {
                throw IllegalArgumentException("Class $kfgClass doesn't match property $property")
            }
            val field = kfgClass.fields.find { it.name == property.propertyName }
                    ?: throw IllegalArgumentException("Class $kfgClass has no property $property")
            term { obj.field(field.type.kexType, field.name).load() }
        }
        else -> when {
            obj.type is KexArray && property.fullName == "length" -> {
                ArrayLengthTerm(KexInt(), obj)
            }
            else -> TODO("Unknown property $property")
        }

    }

    private fun Expr.convertArgs() = args.map { convertTerm(it) }
    private fun List<Term>.combine(combiner: (Term, Term) -> Term): Term = when (size) {
        0, 1 -> throw  IllegalArgumentException("Nothing to combine")
        else -> drop(1).fold(first(), combiner)
    }

    private fun List<PredicateState>.combine(combiner: (PredicateState, PredicateState) -> PredicateState): PredicateState = when (size) {
        0 -> BasicState()
        else -> drop(1).fold(first(), combiner)
    }
}

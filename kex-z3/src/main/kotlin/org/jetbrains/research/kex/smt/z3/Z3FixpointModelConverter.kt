package org.jetbrains.research.kex.smt.z3

import com.abdullin.kthelper.assert.unreachable
import com.abdullin.kthelper.logging.log
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Expr
import com.microsoft.z3.IntExpr
import com.microsoft.z3.IntNum
import com.microsoft.z3.enumerations.Z3_lbool
import org.jetbrains.research.kex.ktype.KexVoid
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.ConstantPropagator
import org.jetbrains.research.kex.state.transformer.Optimizer
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.type.TypeFactory

class Z3FixpointModelConverter(
        private val termVars: Map<Int, Term>,
        private val memspaceVars: Map<Int, Int>,
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


    private fun variableTerm(expr: Expr): Term {
        if (expr.index in termVars) return termVars[expr.index]!!
        if (expr.index in memspaceVars) throw IllegalStateException("Try to convert memory var")
        throw IllegalStateException("Unknown var $expr")
    }

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
        val memspace = memspaceVars[memory.index]
                ?: throw IllegalStateException("Unexpected memspace $memory")
        return when {
            location.isVar -> {
                val locationVariable = variableTerm(location)
                val field = offsetMap(locationVariable)[0]
                        ?: throw IllegalStateException("No field by offset 0")
                val fieldTerm = term { locationVariable.field(field.type.kexType, field.name) }
                term { fieldTerm.load() }
            }
            correctLocationWithOffset(location) -> {
                val locationVariable = variableTerm(locationObject(location))
                val offset = locationOffset(location)
                val field = offsetMap(locationVariable)[offset]
                        ?: throw IllegalStateException("No field by offset $offset")
                val fieldTerm = term { locationVariable.field(field.type.kexType, field.name) }
                term { fieldTerm.load() }
            }
            location is IntNum -> {
                log.warn("Constant pointer in memory")
                val locationVariable = term { value(KexVoid(), "Unknown_${location.int}") }
                val fieldTerm = term { locationVariable.field(KexVoid(), "unknown") }
                term { fieldTerm.load() }
            }
            else -> TODO()
        }
    }

    private fun locationOffset(location: Expr) = with(location) {
        when {
            args[0].isIntNum -> (args[0] as IntNum).int
            args[1].isIntNum -> (args[1] as IntNum).int
            else -> unreachable("Impossible")
        }
    }

    private fun locationObject(location: Expr) = with(location) {
        when {
            args[0].isVar -> args[0]
            args[1].isVar -> args[1]
            else -> unreachable("Impossible")
        }
    }

    private fun correctLocationWithOffset(location: Expr) = with(location) {
        isAdd && numArgs == 2 && ((args[0].isIntNum && args[1].isVar) || (args[1].isIntNum && args[0].isVar))
    }

    private fun offsetMap(obj: Term): Map<Int, Field> {
        val kType = obj.type.getKfgType(tf)
        if (kType !is ClassType) TODO("Only class types supported")
        val kfgClass = kType.`class`
        return kfgClass.fields.map {
            Z3ExprFactory.getFieldOffset(kfgClass, Class.FieldKey("'${it.name}'", it.type)) to it
        }.toMap()
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

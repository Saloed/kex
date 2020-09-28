package org.jetbrains.research.kex.smt.z3.fixpoint.model

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.*
import com.microsoft.z3.enumerations.Z3_decl_kind
import com.microsoft.z3.enumerations.Z3_lbool
import org.jetbrains.research.kex.ktype.*
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.smt.z3.Z3Unlogic
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.Declaration
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.MemoryAccessScope
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.predicate.path
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.Optimizer
import org.jetbrains.research.kex.util.VariableGenerator
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.type.TypeFactory

internal class ConverterContext {
    val callDependencies = hashSetOf<TermDependency>()
    val variableGenerator = VariableGenerator("model")
    val pathVarGenerator = variableGenerator.createNestedGenerator("pv")
    val tmpVarGenerator = variableGenerator.createNestedGenerator("tmp").unique()
    val stateBuilder = StateBuilder()

    fun makePath(term: Term, pathCondition: Boolean): PredicateState {
        val pathVariable = pathVarGenerator.generatorFor(term).createVar(KexBool())
        stateBuilder += state { pathVariable equality term }
        return path { pathVariable equality pathCondition }.wrap()
    }

    fun makePath(builder: TermBuilder.() -> Term, pathCondition: Boolean) = makePath(term { builder() }, pathCondition)
    fun tmpVariable(type: KexType) = tmpVarGenerator.createUniqueVar(type)
}

class FixpointModelConverter(
        private val mapping: ModelDeclarationMapping,
        private val tf: TypeFactory,
        private val z3Context: Z3Context
) {
    private lateinit var converterContext: ConverterContext

    fun apply(expr: Expr): RecoveredModel {
        converterContext = ConverterContext()
        val rawPath = convert(expr.simplify())
        val rawState = converterContext.stateBuilder.apply()
        val state = rawState
                .let { ComparisonNormalizer().apply(it) }
                .let { Optimizer.apply(it) }
                .let { InstanceOfCorrector(z3Context, tf).apply(it) }
                .simplify()
        val path = Optimizer.apply(rawPath)
        analyzeMemoryDependencies(state)
        MemoryUtils.verifyVersions(state)
        return RecoveredModel(
                PredicateStateWithPath(state, path),
                converterContext.callDependencies.toSet(),
                converterContext.pathVarGenerator.generatedVariables().toSet(),
                converterContext.tmpVarGenerator.generatedVariables().toSet()
        )
    }

    private fun analyzeMemoryDependencies(state: PredicateState) = converterContext.callDependencies.plusAssign(
            MemoryUtils.collectMemoryAccesses(state).mapNotNull { memAccess ->
                mapping.callDependentDeclarations[memAccess.descriptor() to memAccess.memoryVersion]
                        ?.let { TermDependency.MemoryDependency(memAccess, it.index, it.predicate) }
            }
    )


    private fun convert(expr: Expr): PredicateState = when (expr) {
        is BoolExpr -> convert(expr)
        else -> error("Try to convert non boolean predicate")
    }

    private fun convert(expr: BoolExpr): PredicateState = when {
        expr.isAnd -> expr.args.map { convert(it) }.combine { a, b -> ChainState(a, b) }.simplify()
        expr.isOr -> ChoiceState(expr.args.map { convert(it) }).simplify()
        expr.isNot && expr.numArgs == 1 -> converterContext.makePath(convertTerm(expr.args.first()), false)
        expr.isEq && expr.numArgs == 2 -> {
            val (lhs, rhs) = expr.convertArgs()
            converterContext.makePath({ lhs eq rhs }, true)
        }
        else -> converterContext.makePath(convertTerm(expr), true)
    }

    private fun convertTerm(expr: Expr): Term = when {
        expr.isVar -> convertVariableTerm(expr)
        expr.isSelect && expr.numArgs == 2 && expr.args[0].isVar -> convertMemoryLoad(expr.args[0], expr.args[1])
        expr.isSelect -> convertComplexMemoryLoad(expr)
        expr.isITE -> convertITETerm(expr)
        expr is BoolExpr -> convertBoolTerm(expr)
        expr is IntExpr -> convertIntTerm(expr)
        expr is BitVecExpr -> convertBVTerm(expr)
        expr is FPExpr -> convertFPTerm(expr)
        expr is RealExpr -> convertRealTerm(expr)
        else -> TODO()
    }

    private fun convertVariableTerm(expr: Expr) = mapping.getTerm(expr.index, converterContext.callDependencies)

    private fun convertBoolTerm(expr: BoolExpr): Term = when {
        expr.isAnd -> expr.convertArgs().combine { a, b -> a and b }
        expr.isOr -> expr.convertArgs().combine { a, b -> a or b }
        expr.isNot && expr.numArgs == 1 -> expr.convertArgs().first().let { term { it.not() } }
        expr.isEq && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a eq b }
        expr.isLE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a le b }
        expr.isGE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a ge b }
        expr.isConst && expr.boolValue == Z3_lbool.Z3_L_TRUE -> term { const(true) }
        expr.isConst && expr.boolValue == Z3_lbool.Z3_L_FALSE -> term { const(false) }
        expr.isBVSLE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a le b }
        expr.isBVSGE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a ge b }
        else -> TODO()
    }

    private fun convertIntTerm(expr: IntExpr): Term = when {
        expr.isIntNum -> term {
            val intExpr = expr as IntNum
            val longValue = intExpr.int64
            when {
                longValue >= Int.MIN_VALUE.toLong() || longValue <= Int.MAX_VALUE.toLong() -> const(longValue.toInt())
                else -> const(longValue)
            }
        }
        expr.isAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isMul -> expr.convertArgs().combine { a, b -> a mul b }
        expr.isRealToInt -> expr.convertArgs().first().let { term { it primitiveAs KexInt() } }
        else -> TODO()
    }

    private fun convertBVTerm(expr: BitVecExpr): Term = when {
        expr is BitVecNum -> Z3Unlogic.undo(expr)
        expr.isBVAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isBVMul -> expr.convertArgs().combine { a, b -> a mul b }
        else -> TODO()
    }

    private fun convertFPTerm(expr: FPExpr): Term = when {
        expr is FPNum -> Z3Unlogic.undo(expr)
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_ADD -> listOf(expr.args[1], expr.args[2]).map { convertTerm(it) }.combine { a, b -> a add b }
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_TO_FP -> convertTerm(expr.args[1])
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_NEG -> convertTerm(expr.args[0]).let { term { it.not() } }
        else -> TODO()
    }

    private fun convertRealTerm(expr: RealExpr): Term = when {
        expr is RatNum -> term { const(expr.numerator.int64.toDouble() / expr.denominator.int64.toDouble()) }
        expr.isAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isMul -> expr.convertArgs().combine { a, b -> a mul b }
        expr.isIntToReal -> expr.convertArgs().first().let { term { it primitiveAs KexDouble() } }
        expr.isApp && (expr.funcDecl.name as? StringSymbol)?.string == "fp.to_real" -> expr.convertArgs().first()
        else -> TODO("Real: $expr")
    }

    private fun convertITETerm(expr: Expr): Term {
        val (condition, trueBranch, falseBranch) = expr.convertArgs()
        check(trueBranch.type == falseBranch.type) { "Types of expression branches must be equal" }
        return IfTerm(trueBranch.type, condition, trueBranch, falseBranch)
    }

    private fun convertComplexMemoryLoad(expr: Expr): Term {
        log.warn("Load from complex memory")
        val ctx = z3Context.factory.ctx
        val params = ctx.mkParams().apply {
            add("expand_store_eq", true)
            add("expand_select_store", true)
            add("elim_ite", true)
            add("ite_extra_rules", true)
        }
        val simplified = expr.simplify(params)
        if (!simplified.isSelect) return convertTerm(simplified)
        if (simplified.numArgs != 2) error("Unexpected select arguments")
        val (memoryExpr, locationExpr) = simplified.args
        if (memoryExpr.isVar) return convertTerm(simplified)
        val (_, memoryDecl) = convertComplexMemoryExpr(memoryExpr)
        return convertMemoryLoad(memoryDecl, locationExpr)
    }

    private fun convertComplexMemoryExpr(expr: Expr) = when {
        expr.isITE -> convertComplexMemoryITE(expr)
        expr is ArrayExpr -> convertComplexMemoryArray(expr)
        else -> TODO()
    }

    private fun convertComplexMemoryArray(expr: ArrayExpr): Pair<Term, Declaration.Memory> = when {
        expr.isVar -> {
            val decl = mapping.arguments[expr.index] as? Declaration.Memory
                    ?: error("Non memory declaration")
            term { const(true) } to decl
        }
        expr.isStore && expr.numArgs == 3 -> {
            val (memory, location, value) = expr.args
            convertComplexMemoryArrayStore(memory, location, value)
        }
        else -> TODO()
    }

    private fun convertComplexMemoryArrayStore(memoryExpr: Expr, locationExpr: Expr, valueExpr: Expr): Pair<Term, Declaration.Memory> {
        val (_, memoryDecl) = convertComplexMemoryExpr(memoryExpr)
        val location = convertTerm(locationExpr)
        val value = convertTerm(valueExpr)
        when (memoryDecl.descriptor.memoryType) {
            MemoryType.PROPERTY -> {
                val (owner, cls, propertyName) = preprocessClassProperty(memoryDecl, location)
                val propertyLoad = getFieldLoad(owner, cls, propertyName, memoryDecl.version, memoryDecl.descriptor.scopeInfo)
                val valueStorePc = converterContext.tmpVariable(KexBool())
                converterContext.stateBuilder += basic {
                    state { valueStorePc equality (propertyLoad eq value) }
                }
                return valueStorePc to memoryDecl
            }
            else -> TODO()
        }
    }

    private fun convertComplexMemoryITE(expr: Expr): Pair<Term, Declaration.Memory> {
        val (condExpr, trueExpr, falseExpr) = expr.args
        val condition = convertTerm(condExpr)
        val (trueBranch, trueDecl) = convertComplexMemoryExpr(trueExpr)
        val (falseBranch, falseDecl) = convertComplexMemoryExpr(falseExpr)
        check(trueDecl == falseDecl) { "Different memory declarations" }
        check(trueBranch.type == falseBranch.type) { "Different types in branches" }
        converterContext.stateBuilder += choice({
            path { condition equality true }
            path { trueBranch equality true }
        }, {
            path { condition equality false }
            path { falseBranch equality true }
        })
        return term { const(true) } to trueDecl
    }

    private fun convertMemoryLoad(memory: Expr, location: Expr): Term {
        check(memory.isVar) { "Memory is not var $memory" }
        val decl = mapping.arguments[memory.index] as? Declaration.Memory
                ?: error("Non memory descriptor")
        return convertMemoryLoad(decl, location)
    }

    private fun convertMemoryLoad(decl: Declaration.Memory, location: Expr): Term = when (decl.descriptor.memoryType) {
        MemoryType.PROPERTY -> {
            val (owner, cls, propertyName) = preprocessClassProperty(decl, convertTerm(location))
            getFieldLoad(owner, cls, propertyName, decl.version, decl.descriptor.scopeInfo)
        }
        MemoryType.ARRAY -> {
            if (!(location.isAdd && location.args.size == 2)) {
                throw IllegalStateException("Unexpected array memory location $location")
            }
            val (lhs, rhs) = location.convertArgs()
            val (base, index) = when {
                lhs.type is KexArray -> lhs to rhs
                rhs.type is KexArray -> rhs to lhs
                else -> throw IllegalStateException("Array load has no base and index")
            }
            term { tf.getArrayIndex(base, index).load().withMemoryVersion(decl.version).withScopeInfo(decl.descriptor.scopeInfo) }
        }
        MemoryType.SPECIAL -> when (decl.descriptor.memoryName) {
            InstanceOfTerm.TYPE_MEMORY_NAME -> InstanceOfTerm(UnknownType, convertTerm(location), decl.version)
            ArrayLengthTerm.ARRAY_LENGTH_MEMORY_NAME -> ArrayLengthTerm(KexInt(), convertTerm(location), decl.version)
            else -> error("Unknown special memory ${decl.descriptor}")
        }
        else -> throw IllegalStateException("Unexpected memory $decl")
    }

    private fun preprocessClassProperty(property: Declaration.Memory, obj: Term): Triple<Term, Class, String> {
        val owner = when {
            obj.type.getKfgType(tf) is ClassType -> obj
            obj is ConstIntTerm -> {
                val objId = obj.value
                val identifier = z3Context.getLocals().entries
                        .firstOrNull { (_, id) -> id == objId }?.key
                        ?: error("No info about object $objId")
                LocalObjectTerm("local__$objId", identifier)
            }
            else -> throw IllegalArgumentException("Only class types supported")
        }
        val (className, propertyName) = property.classPropertyNames()
        return Triple(owner, tf.cm[className], propertyName)
    }

    private fun getFieldLoad(owner: Term, cls: Class, fieldName: String, version: MemoryVersion, scope: MemoryAccessScope): Term {
        val (fields, fieldType) = cls.property(fieldName)
        if (fields.size == 1) {
            val field = fields.first()
            return term { owner.field(fieldType, field.name).load().withMemoryVersion(version).withScopeInfo(scope) }
        }
        val resultFiledLoad = converterContext.tmpVariable(fieldType)
        // todo: maybe add default type choice
        val axioms = fields.map {
            val type = it.`class`.kexType
            val tmpVar = converterContext.tmpVariable(type)
            basic {
                path { owner.instanceOf(it.`class`, version, scope) equality const(true) }
                state { tmpVar equality owner }
                state {
                    resultFiledLoad equality tmpVar.field(it.type.kexType, it.name).load().withMemoryVersion(version).withScopeInfo(scope)
                }
            }
        }
        converterContext.stateBuilder += ChoiceState(axioms)
        return resultFiledLoad
    }

    private fun Term.instanceOf(cls: Class, version: MemoryVersion, scope: MemoryAccessScope): Term = cls.allInheritors()
            .map { it.kexType }
            .map { term { tf.getInstanceOf(it, this@instanceOf).withMemoryVersion(version).withScopeInfo(scope) } }
            .combine { t1, t2 -> t1 or t2 }

    private fun Expr.convertArgs() = args.map { convertTerm(it) }
    private fun List<Term>.combine(combiner: TermBuilder.(Term, Term) -> Term) = reduce { acc, term -> TermBuilder.Terms.combiner(acc, term) }

    private fun List<PredicateState>.combine(combiner: (PredicateState, PredicateState) -> PredicateState) = reduceOrNull(combiner)
            ?: BasicState()

}

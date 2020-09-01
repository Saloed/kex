package org.jetbrains.research.kex.smt.z3.fixpoint

import com.abdullin.kthelper.logging.log
import com.microsoft.z3.*
import com.microsoft.z3.enumerations.Z3_decl_kind
import com.microsoft.z3.enumerations.Z3_lbool
import org.jetbrains.research.kex.ktype.KexArray
import org.jetbrains.research.kex.ktype.KexDouble
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.Z3Context
import org.jetbrains.research.kex.smt.z3.Z3Unlogic
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.MemoryAccessScope
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryUtils
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.Optimizer
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.ConcreteClass
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.ir.OuterClass
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.type.TypeFactory

class FixpointModelConverter(
        private val mapping: ModelDeclarationMapping,
        private val tf: TypeFactory,
        private val z3Context: Z3Context
) {
    private var callDependencies = hashSetOf<TermDependency>()

    fun apply(expr: Expr): RecoveredModel {
        callDependencies = hashSetOf()
        val state = expr.simplify()
                .let { convert(it) }
                .let { ComparisonNormalizer().apply(it) }
                .let { Optimizer().apply(it) }
                .let { InstanceOfCorrector(z3Context).apply(it) }
                .simplify()
        analyzeMemoryDependencies(state)
        MemoryUtils.verifyVersions(state)
        return RecoveredModel(state, callDependencies.toSet())
    }

    private fun analyzeMemoryDependencies(state: PredicateState) = callDependencies.plusAssign(
            MemoryUtils.collectMemoryAccesses(state)
                    .mapNotNull { memAccess -> mapping.callDependentDeclarations[memAccess.descriptor() to memAccess.memoryVersion]?.let { TermDependency.MemoryDependency(memAccess, it.index, it.predicate) } }
    )


    private fun convert(expr: Expr): PredicateState = when (expr) {
        is BoolExpr -> convert(expr)
        else -> convertTerm(expr).equality { const(true) }
    }

    private fun convert(expr: BoolExpr): PredicateState = when {
        expr.isAnd -> expr.args.map { convert(it) }.combine { a, b -> ChainState(a, b) }.simplify()
        expr.isOr -> ChoiceState(expr.args.map { convert(it) }).simplify()
        expr.isNot && expr.numArgs == 1 -> convertTerm(expr.args.first()).equality { const(false) }
        expr.isEq && expr.numArgs == 2 -> {
            val (lhs, rhs) = expr.convertArgs()
            lhs.equality(rhs)
        }
        else -> convertTerm(expr).equality { const(true) }
    }

    private fun convertTerm(expr: Expr): TermWithAxiom = when {
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

    private fun convertVariableTerm(expr: Expr): TermWithAxiom = mapping.getTerm(expr.index, callDependencies)

    private fun convertBoolTerm(expr: BoolExpr): TermWithAxiom = when {
        expr.isAnd -> expr.convertArgs().combine { a, b -> a and b }
        expr.isOr -> expr.convertArgs().combine { a, b -> a or b }
        expr.isNot && expr.numArgs == 1 -> expr.convertArgs().first().transformTerm { it.not() }
        expr.isEq && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a eq b }
        expr.isLE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a le b }
        expr.isGE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a ge b }
        expr.isConst && expr.boolValue == Z3_lbool.Z3_L_TRUE -> TermWithAxiom.wrap { const(true) }
        expr.isConst && expr.boolValue == Z3_lbool.Z3_L_FALSE -> TermWithAxiom.wrap { const(false) }
        expr.isBVSLE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a le b }
        expr.isBVSGE && expr.numArgs == 2 -> expr.convertArgs().combine { a, b -> a ge b }
        else -> TODO()
    }

    private fun convertIntTerm(expr: IntExpr): TermWithAxiom = when {
        expr.isIntNum -> TermWithAxiom.wrap {
            val intExpr = expr as IntNum
            val longValue = intExpr.int64
            when {
                longValue >= Int.MIN_VALUE.toLong() || longValue <= Int.MAX_VALUE.toLong() -> const(longValue.toInt())
                else -> const(longValue)
            }
        }
        expr.isAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isMul -> expr.convertArgs().combine { a, b -> a mul b }
        expr.isRealToInt -> expr.convertArgs().first().transformTerm { it primitiveAs KexInt() }
        else -> TODO()
    }

    private fun convertBVTerm(expr: BitVecExpr): TermWithAxiom = when {
        expr is BitVecNum -> TermWithAxiom.wrap { Z3Unlogic.undo(expr) }
        expr.isBVAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isBVMul -> expr.convertArgs().combine { a, b -> a mul b }
        else -> TODO()
    }

    private fun convertFPTerm(expr: FPExpr): TermWithAxiom = when {
        expr is FPNum -> TermWithAxiom.wrap { Z3Unlogic.undo(expr) }
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_ADD -> listOf(expr.args[1], expr.args[2]).map { convertTerm(it) }.combine { a, b -> a add b }
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_TO_FP -> convertTerm(expr.args[1])
        expr.isApp && expr.funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_NEG -> convertTerm(expr.args[0]).transformTerm { it.not() }
        else -> TODO()
    }

    private fun convertRealTerm(expr: RealExpr): TermWithAxiom = when {
        expr is RatNum -> TermWithAxiom.wrap { const(expr.numerator.int64.toDouble() / expr.denominator.int64.toDouble()) }
        expr.isAdd -> expr.convertArgs().combine { a, b -> a add b }
        expr.isMul -> expr.convertArgs().combine { a, b -> a mul b }
        expr.isIntToReal -> expr.convertArgs().first().transformTerm { it primitiveAs KexDouble() }
        expr.isApp && (expr.funcDecl.name as? StringSymbol)?.string == "fp.to_real" -> expr.convertArgs().first()
        else -> TODO("Real: $expr")
    }

    private fun convertITETerm(expr: Expr): TermWithAxiom {
        val (condition, trueBranch, falseBranch) = expr.convertArgs()
        check(trueBranch.term.type == falseBranch.term.type) { "Types of expression branches must be equal" }
        return TermWithAxiom.wrap { IfTerm(trueBranch.term.type, condition.term, trueBranch.term, falseBranch.term) }.mergeAxioms(condition, trueBranch, falseBranch)
    }

    private fun convertComplexMemoryLoad(expr: Expr): TermWithAxiom {
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
        val (memory, memoryDecl) = convertComplexMemoryExpr(memoryExpr)
        val result = convertMemoryLoad(memoryDecl, locationExpr)
        return memory.binaryOperation(result) { _, res -> res }
    }

    private fun convertComplexMemoryExpr(expr: Expr) = when {
        expr.isITE -> convertComplexMemoryITE(expr)
        expr is ArrayExpr -> convertComplexMemoryArray(expr)
        else -> TODO()
    }

    private fun convertComplexMemoryArray(expr: ArrayExpr) = when {
        expr.isVar -> {
            val decl = mapping.declarations[expr.index] as? Declaration.Memory
                    ?: error("Non memory declaration")
            val term = TermWithAxiom.wrap { const(true) }
            term to decl
        }
        expr.isStore && expr.numArgs == 3 -> {
            val (memory, location, value) = expr.args
            convertComplexMemoryArrayStore(memory, location, value)
        }
        else -> TODO()
    }

    private fun convertComplexMemoryArrayStore(memoryExpr: Expr, locationExpr: Expr, valueExpr: Expr): Pair<TermWithAxiom, Declaration.Memory> {
        val (memory, memoryDecl) = convertComplexMemoryExpr(memoryExpr)
        val location = convertTerm(locationExpr)
        val value = convertTerm(valueExpr)
        when (memoryDecl.descriptor.memoryType) {
            MemoryType.PROPERTY -> {
                val (owner, cls, propertyName) = preprocessClassProperty(memoryDecl, location)
                val field = cls.findField(propertyName) ?: error("No field found")
                val axiom = basic {
                    state { owner.term.field(field.type.kexType, field.name).store(value.term).withMemoryVersion(memoryDecl.version).withScopeInfo(memoryDecl.descriptor.scopeInfo) }
                }
                val term = TermWithAxiom(term { const(true) }, axiom).mergeAxioms(memory, location, value)
                return term to memoryDecl
            }
            else -> TODO()
        }
    }

    private fun convertComplexMemoryITE(expr: Expr): Pair<TermWithAxiom, Declaration.Memory> {
        val (condExpr, trueExpr, falseExpr) = expr.args
        val condition = convertTerm(condExpr)
        val (trueBranch, trueDecl) = convertComplexMemoryExpr(trueExpr)
        val (falseBranch, falseDecl) = convertComplexMemoryExpr(falseExpr)
        check(trueDecl == falseDecl) { "Different memory declarations" }
        check(trueBranch.term.type == falseBranch.term.type) { "Different types in branches" }
        val trueCondition = basic { path { condition.term equality true } }
        val falseCondition = basic { path { condition.term equality false } }
        val result = term { value(trueBranch.term.type, "ite__${expr.hashCode()}") }
        val trueAxiom = listOfNotNull(condition.axiom, trueCondition, trueBranch.axiom, basic { state { result equality trueBranch.term } }).reduce { acc, ps -> ChainState(acc, ps) }
        val falseAxiom = listOfNotNull(condition.axiom, falseCondition, falseBranch.axiom, basic { state { result equality falseBranch.term } }).reduce { acc, ps -> ChainState(acc, ps) }
        val axiom = ChoiceState(listOf(trueAxiom, falseAxiom))
        return TermWithAxiom(result, axiom) to trueDecl
    }

    private fun convertMemoryLoad(memory: Expr, location: Expr): TermWithAxiom {
        check(memory.isVar) { "Memory is not var $memory" }
        val decl = mapping.declarations[memory.index] as? Declaration.Memory
                ?: error("Non memory descriptor")
        return convertMemoryLoad(decl, location)
    }

    private fun convertMemoryLoad(decl: Declaration.Memory, location: Expr): TermWithAxiom = when (decl.descriptor.memoryType) {
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
                lhs.term.type is KexArray -> lhs to rhs
                rhs.term.type is KexArray -> rhs to lhs
                else -> throw IllegalStateException("Array load has no base and index")
            }
            base.binaryOperation(index) { b, i -> tf.getArrayIndex(b, i).load().withMemoryVersion(decl.version).withScopeInfo(decl.descriptor.scopeInfo) }
        }
        MemoryType.SPECIAL -> when (decl.descriptor.memoryName) {
            InstanceOfTerm.TYPE_MEMORY_NAME -> convertTerm(location).transformTerm { InstanceOfTerm(UnknownType, it, decl.version) }
            ArrayLengthTerm.ARRAY_LENGTH_MEMORY_NAME -> convertTerm(location).transformTerm { ArrayLengthTerm(KexInt(), it, decl.version) }
            else -> error("Unknown special memory ${decl.descriptor}")
        }
        else -> throw IllegalStateException("Unexpected memory $decl")
    }

    private fun preprocessClassProperty(property: Declaration.Memory, obj: TermWithAxiom): Triple<TermWithAxiom, Class, String> {
        val owner = when {
            obj.term.type.getKfgType(tf) is ClassType -> obj
            obj.term is ConstIntTerm -> {
                val objId = obj.term.value
                val identifier = z3Context.getLocals().entries
                        .firstOrNull { (_, id) -> id == objId }?.key
                        ?: error("No info about object $objId")
                TermWithAxiom.wrap { LocalObjectTerm("local__$objId", identifier) }
            }
            else -> throw IllegalArgumentException("Only class types supported")
        }
        val (className, propertyName) = property.classPropertyNames()
        return Triple(owner, tf.cm[className], propertyName)
    }

    private fun getFieldLoad(owner: TermWithAxiom, cls: Class, fieldName: String, version: MemoryVersion, scope: MemoryAccessScope): TermWithAxiom {
        val field = cls.findField(fieldName)
        if (field != null) {
            return owner.transformTerm { it.field(field.type.kexType, field.name).load().withMemoryVersion(version).withScopeInfo(scope) }
        }
        val fields = tf.cm.concreteClasses
                .filter { it.isInheritorOf(cls) }
                .mapNotNull { it.findField(fieldName) }
                .toSet()
        if (fields.isEmpty()) throw IllegalArgumentException("Class $cls and it inheritors has no field $fieldName")
        val fieldType = fields.map { it.type.kexType }.groupBy({ it }, { 1 }).maxByOrNull { (_, cnt) -> cnt.sum() }?.key
                ?: throw IllegalStateException("No types")
        val resultFiledLoad = term { value(fieldType, "load_${cls.name}.$fieldName") }
        val axioms = fields.map {
            val type = it.`class`.kexType
            val tmpVar = term { value(type, "${resultFiledLoad.name}_as_${type.name}") }
            basic {
                path {
                    owner.term.instanceOf(it.`class`, version, scope) equality const(true)
                }
                state {
                    tmpVar.cast(owner.term, type).withMemoryVersion(version).withScopeInfo(scope)
                }
                state {
                    resultFiledLoad equality tmpVar.field(it.type.kexType, it.name).load().withMemoryVersion(version).withScopeInfo(scope)
                }
            }
        }
        val result = TermWithAxiom(resultFiledLoad, ChoiceState(axioms))
        return owner.binaryOperation(result) { _, fieldLoad -> fieldLoad }
    }

    private fun Term.instanceOf(cls: Class, version: MemoryVersion, scope: MemoryAccessScope): Term = cls.allInheritors()
            .map { it.kexType }
            .map { term { tf.getInstanceOf(it, this@instanceOf).withMemoryVersion(version).withScopeInfo(scope) } }
            .reduce { t1: Term, t2: Term -> term { t1 or t2 } }

    private fun Class.allInheritors() = cm.concreteClasses.filter { it.isInheritorOf(this) }.toSet()

    private fun Expr.convertArgs() = args.map { convertTerm(it) }
    private fun List<TermWithAxiom>.combine(combiner: TermBuilder.(Term, Term) -> Term): TermWithAxiom = when (size) {
        0, 1 -> throw  IllegalArgumentException("Nothing to combine")
        else -> drop(1).fold(first()) { acc, term -> acc.binaryOperation(term, combiner) }
    }

    private fun List<PredicateState>.combine(combiner: (PredicateState, PredicateState) -> PredicateState): PredicateState = when (size) {
        0 -> BasicState()
        else -> drop(1).fold(first(), combiner)
    }

    private fun Class.findFieldConcrete(name: String): Field? {
        return fields.find { it.name == name } ?: superClass?.findFieldConcrete(name)
    }

    private fun Class.findField(name: String): Field? {
        val myField = fields.find { it.name == name }
        if (myField != null) return myField
        var parents = (listOf(superClass) + interfaces).filterNotNull()

        var result = parents.mapNotNull { it as? ConcreteClass }.mapNotNull { it.findFieldConcrete(name) }.firstOrNull()
        while (parents.isNotEmpty()) {
            if (result != null) break
            parents = parents
                    .map { (listOf(it.superClass) + it.interfaces).filterNotNull() }
                    .flatten()
            result = parents.mapNotNull { it as? ConcreteClass }.mapNotNull { it.findFieldConcrete(name) }.firstOrNull()
        }

        return result
                ?: (listOf(superClass) + interfaces).filterNotNull().mapNotNull { it as? OuterClass }.map { it.findFieldConcrete(name) }.firstOrNull()

    }

    private fun TermWithAxiom.mergeAxioms(vararg other: TermWithAxiom): TermWithAxiom =
            other.fold(this) { result, current -> result.binaryOperation(current) { res, _ -> res } }
}

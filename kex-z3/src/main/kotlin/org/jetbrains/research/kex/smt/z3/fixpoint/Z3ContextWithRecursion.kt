package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.MemoryVersion
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.FieldLoadTerm
import org.jetbrains.research.kex.state.transformer.memspace
import org.jetbrains.research.kfg.ir.Field
import org.jetbrains.research.kfg.type.TypeFactory

class Z3ContextWithRecursion(
        private val recursiveCalls: Map<CallPredicate, Map<Field, FieldLoadTerm>>,
        callPrototype: CallPredicate,
        private val predicateName: String, tf: TypeFactory) : Z3Converter(tf) {

    private val orderedDeclarations: MutableList<DeclarationTracker.Declaration>
    private val orderedProperties: List<DeclarationTracker.Declaration.NormalProperty>
    private val propertyTypes = hashMapOf<DeclarationTracker.Declaration.NormalProperty, KexType>()
    val mapper: ModelDeclarationMapping

    init {
        val receiver = callPrototype.lhvUnsafe
                ?: throw IllegalStateException("Call prototype must have a receiver")
        val call = callPrototype.call as CallTerm
        val argumentDecls = call.arguments.mapIndexed { index, _ -> DeclarationTracker.Declaration.Argument(index) }
        val ownerDecl = DeclarationTracker.Declaration.This()
        val receiverDecl = DeclarationTracker.Declaration.Other()
        orderedProperties = prepareMemoryProperties()
        orderedDeclarations = (listOf(ownerDecl) + argumentDecls + listOf(receiverDecl) + orderedProperties).toMutableList()
        mapper = ModelDeclarationMapping(orderedDeclarations)
        argumentDecls.zip(call.arguments).forEach { (decl, term) -> mapper.setTerm(decl, term) }
        mapper.setTerm(ownerDecl, call.owner)
        mapper.setTerm(receiverDecl, receiver)
    }

    override fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context): Bool_ = when {
        call in recursiveCalls -> buildPredicate(call, ef, ctx)
        else -> ef.makeTrue()
    }

    fun buildPredicate(callPredicate: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context): Z3Bool {
        val predicateArguments = predicateArguments(callPredicate, ef, ctx)
        val predicateSorts = predicateArguments.map { it.getSort() }
        val predicateAxioms = predicateArguments.map { it.axiom }
        val predicateExprs = predicateArguments.map { it.expr }
        val predicate = ef.ctx.mkFuncDecl(predicateName, predicateSorts.toTypedArray(), ef.ctx.mkBoolSort())
        val predicateApplication = ef.ctx.mkApp(predicate, *predicateExprs.toTypedArray()) as BoolExpr
        return Z3Bool(ef.ctx, predicateApplication, spliceAxioms(ef.ctx, predicateAxioms))
    }

    private fun prepareMemoryProperties(): List<DeclarationTracker.Declaration.NormalProperty> {
        val allCallProperties = recursiveCalls.values
        val propertyPrototype = allCallProperties.first()
        if (allCallProperties.any { it != propertyPrototype }) {
            TODO("Recursion with different memory properties")
        }
        return propertyPrototype.map { (field, loadTerm) ->
            val property = DeclarationTracker.Declaration.NormalClassProperty(field.`class`.fullname, field.name, 0, loadTerm.field.memspace)
            propertyTypes[property] = loadTerm.type
            property
        }
    }

    private fun predicateArguments(callPredicate: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context): List<Z3ValueExpr> {
        val call = callPredicate.call as CallTerm
        val arguments = (listOf(call.owner) + call.arguments).map { convert(it, ef, ctx) }
        val receiver = callPredicate.lhvUnsafe?.let { convert(it, ef, ctx) } ?: ef.dummyReceiver(call)
        return (arguments
                + listOf(receiver)
                + orderedProperties.map { readProperty(it, ef, ctx) }
                )
    }

    private fun readProperty(property: DeclarationTracker.Declaration.NormalProperty, ef: Z3ExprFactory, ctx: Z3Context): Z3ValueExpr {
        val type = Z3Type(propertyTypes[property]!!)
        val memory = ctx.getProperties(property.fullName, MemoryVersion.initial(), property.memspace,  type).memory
        memory.load<Z3ValueExpr>(Z3BV32.makeConst(ef.ctx, 0), type) // force array creation for empty memory
        return memory.inner
    }

    private fun Z3ExprFactory.dummyReceiver(call: CallTerm) = getVarByTypeAndName(call.method.returnType.kexType, "dummy_result_receiver", fresh = true)

}
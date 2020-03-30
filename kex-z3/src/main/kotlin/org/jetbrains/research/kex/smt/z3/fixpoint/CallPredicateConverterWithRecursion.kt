package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.FieldLoadTerm
import org.jetbrains.research.kex.state.transformer.memspace
import org.jetbrains.research.kfg.ir.Field

class CallPredicateConverterWithRecursion(
        private val recursiveCalls: Map<CallPredicate, Map<Field, FieldLoadTerm>>,
        callPrototype: CallPredicate,
        private val predicateName: String) {

    private val orderedDeclarations: MutableList<DeclarationTracker.Declaration>
    private val orderedProperties: List<DeclarationTracker.Declaration.Property>
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

    fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool =
            when {
                call in recursiveCalls -> buildPredicate(call, ef, ctx, converter)
                else -> ef.makeTrue()
            }

    fun buildPredicate(callPredicate: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool {
        val predicateArguments = predicateArguments(callPredicate, converter, ef, ctx)
        val predicateSorts = predicateArguments.map { it.getSort() }
        val predicateAxioms = predicateArguments.map { it.axiom }
        val predicateExprs = predicateArguments.map { it.expr }
        val predicate = ef.ctx.mkFuncDecl(predicateName, predicateSorts.toTypedArray(), ef.ctx.mkBoolSort())
        val predicateApplication = ef.ctx.mkApp(predicate, *predicateExprs.toTypedArray()) as BoolExpr
        return Z3Bool(ef.ctx, predicateApplication, spliceAxioms(ef.ctx, predicateAxioms))
    }

    private fun prepareMemoryProperties(): List<DeclarationTracker.Declaration.Property> {
        val allCallProperties = recursiveCalls.values
        val propertyPrototype = allCallProperties.first()
        if (allCallProperties.any { it != propertyPrototype }) {
            TODO("Recursion with different memory properties")
        }
        return propertyPrototype.map { (field, loadTerm) ->
            DeclarationTracker.Declaration.ClassProperty(field.`class`.fullname, field.name, loadTerm.field.memspace)
        }
    }

    private fun predicateArguments(callPredicate: CallPredicate, converter: Z3Converter, ef: Z3ExprFactory, ctx: Z3Context): List<Z3ValueExpr> {
        val call = callPredicate.call as CallTerm
        val arguments = (listOf(call.owner) + call.arguments).map { converter.convert(it, ef, ctx) }
        val receiver = callPredicate.lhvUnsafe?.let { converter.convert(it, ef, ctx) } ?: ef.dummyReceiver(call)
        return (arguments
                + listOf(receiver)
                + orderedProperties.map { ctx.getProperties(it.memspace, it.fullName) }.map { it.memory.inner }
                )
    }

    private fun Z3ExprFactory.dummyReceiver(call: CallTerm) = getVarByTypeAndName(call.method.returnType.kexType, "dummy_result_receiver", fresh = true)

}

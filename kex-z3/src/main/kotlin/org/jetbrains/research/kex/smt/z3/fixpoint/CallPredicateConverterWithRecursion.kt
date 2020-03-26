package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.BoolExpr
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.FieldLoadTerm
import org.jetbrains.research.kex.state.transformer.memspace
import org.jetbrains.research.kfg.ir.Field

class CallPredicateConverterWithRecursion(val recursiveCalls: Map<CallPredicate, Map<Field, FieldLoadTerm>>, val predicateName: String) {

    lateinit var orderedProperties: List<DeclarationTracker.Declaration.Property>

    fun convert(call: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool =
            when {
                call in recursiveCalls -> buildPredicate(call, ef, ctx, converter)
                else -> ef.makeTrue()
            }

    fun initializeAndCreateMapping(callPredicate: CallPredicate): ModelDeclarationMapping {
        val receiver = callPredicate.lhvUnsafe
                ?: throw IllegalStateException("Call prototype must have a receiver")
        val call = callPredicate.call as CallTerm
        val argumentDecls = call.arguments.mapIndexed { index, term -> DeclarationTracker.Declaration.Argument(index) }
        val ownerDecl = DeclarationTracker.Declaration.Other()
        val receiverDecl = DeclarationTracker.Declaration.Other()
        orderedProperties = prepareMemoryProperties()
        val orderedDeclarations = listOf(ownerDecl) + argumentDecls + listOf(receiverDecl) + orderedProperties
        val mapper = ModelDeclarationMapping(orderedDeclarations)
        argumentDecls.zip(call.arguments).forEach { (decl, term) -> mapper.setTerm(decl, term) }
        mapper.setTerm(ownerDecl, call.owner)
        mapper.setTerm(receiverDecl, receiver)
        return mapper
    }

    private fun prepareMemoryProperties(): List<DeclarationTracker.Declaration.Property> {
        val allCallProperties = recursiveCalls.values
        val propertyPrototype = allCallProperties.first()
        if (allCallProperties.any { it != propertyPrototype }) {
            TODO("Recursion with different memory properties")
        }
        return propertyPrototype.map { (field, loadTerm) ->
            DeclarationTracker.Declaration.ClassProperty(field.`class`.name, field.name, loadTerm.field.memspace)
        }
    }


    fun buildPredicate(callPredicate: CallPredicate, ef: Z3ExprFactory, ctx: Z3Context, converter: Z3Converter): Z3Bool {
        val receiver = callPredicate.lhvUnsafe?.let { converter.convert(it, ef, ctx) }
                ?: ef.dummyReceiver(callPredicate.call as CallTerm)
        val arguments = callArguments(callPredicate.call as CallTerm).map { converter.convert(it, ef, ctx) }
        val propertyArrays = orderedProperties.map {ctx.getProperties(it.memspace, it.fullName)}.map { it.memory.inner }
        val predicateArguments = arguments + receiver + propertyArrays
        val predicateSorts = predicateArguments.map { it.getSort() }
        val predicateAxioms = predicateArguments.map { it.axiom }
        val predicateExprs = predicateArguments.map { it.expr }
        val predicate = ef.ctx.mkFuncDecl(predicateName, predicateSorts.toTypedArray(), ef.ctx.mkBoolSort())
        val predicateApplication = ef.ctx.mkApp(predicate, *predicateExprs.toTypedArray()) as BoolExpr
        return Z3Bool(ef.ctx, predicateApplication, spliceAxioms(ef.ctx, predicateAxioms))
    }

    private fun callArguments(call: CallTerm) = listOf(call.owner) + call.arguments
    private fun Z3ExprFactory.dummyReceiver(call: CallTerm) = getVarByTypeAndName(call.method.returnType.kexType, "dummy_result_receiver", fresh = true)

}

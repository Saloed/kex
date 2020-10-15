package org.jetbrains.research.kex.smt.z3.fixpoint.converter

import com.microsoft.z3.Expr
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.Sort
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.Declaration
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.DeclarationTracker
import org.jetbrains.research.kex.state.CallApproximationState
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kfg.type.TypeFactory

class Z3ConverterWithRecursionSupport(
        tf: TypeFactory,
        memoryVersionInfo: MemoryVersionInfo,
        private val recursiveCalls: Set<CallPredicate>,
        val recursionPredicate: Z3FixpointSolver.Predicate
) : Z3ConverterWithCallMemory(tf, memoryVersionInfo) {

    private lateinit var z3RecursionPredicateUnsafe: Predicate

    override fun convert(callApproximation: CallApproximationState, ef: Z3ExprFactory, ctx: Z3Context, extractPath: Boolean): Bool_ {
        if (callApproximation.call !in recursiveCalls) return super.convert(callApproximation, ef, ctx, extractPath)
        check(callApproximation.preconditions.isEmpty()) { "Recursive call with preconditions" }
        val call = callApproximation.call
        val z3RecursionPredicate = buildPredicate(ef, ctx)
        if (call !in callInfo) {
            callInfo[call] = processCall(call, ef, ctx)
        }
        val callInfo = callInfo.getValue(call)
        val callArguments = call.callTerm.subterms.map { convert(it, ef, ctx) }

        val (memoryBeforeCall, memoryAfterCall) = updateCallMemory(callApproximation, ef, ctx)

        val returnValue = convert(callInfo.resultTerm, ef, ctx)
        val predicateApp = z3RecursionPredicate.apply(
                ef,
                callArguments.first(), callArguments.drop(1), returnValue,
                memoryBeforeCall, memoryAfterCall
        )
        return predicateApp and callInfo.result
    }

    private fun updateCallMemory(
            callApproximation: CallApproximationState,
            ef: Z3ExprFactory,
            ctx: Z3Context
    ): Pair<Map<MemoryDescriptor, VersionedMemory>, Map<MemoryDescriptor, VersionedMemory>> {
        convertChoices(emptyList(), ef, ctx)
        val memoryBeforeCall = ctx.getActive()
        ctx.resetMemoryToVersion(callApproximation.call.memoryVersion, memoryVersionInfo)
        val memoryAfterCall = ctx.getActive()
        convert(callApproximation.defaultPostcondition.state, ef, ctx)
        convertChoices(listOf(callApproximation.defaultPostcondition.path), ef, ctx)
        return memoryBeforeCall to memoryAfterCall
    }

    private fun buildPredicate(ef: Z3ExprFactory, ctx: Z3Context): Predicate {
        if (::z3RecursionPredicateUnsafe.isInitialized) return z3RecursionPredicateUnsafe
        val callPrototype = recursiveCalls.first().callTerm
        val ownerSort = callPrototype.owner.type.z3Sort(ef)
        val argumentSorts = callPrototype.arguments.map { it.type.z3Sort(ef) }
        val returnType = callPrototype.method.returnType.kexType
        val returnSort = returnType.z3Sort(ef)
        val memoryDescriptors = memoryVersionInfo.allMemoryVersions.keys.toList()
        val memorySorts = memoryDescriptors.map { it.z3Sort(ctx) }
        val allArgumentSorts = listOf(ownerSort) + argumentSorts + memorySorts + listOf(returnSort) + memorySorts
        val funDecl = ef.ctx.mkFuncDecl(recursionPredicate.name, allArgumentSorts.toTypedArray(), ef.ctx.mkBoolSort())
        z3RecursionPredicateUnsafe = Predicate(funDecl, memoryDescriptors, returnType)
        return z3RecursionPredicateUnsafe
    }

    data class Predicate(
            val decl: FuncDecl,
            val memoryDescriptors: List<MemoryDescriptor>,
            val returnValueType: KexType
    ) {
        fun apply(
                ef: Z3ExprFactory,
                owner: Dynamic_, arguments: List<Dynamic_>, returnValue: Dynamic_,
                inputMemory: Map<MemoryDescriptor, VersionedMemory>, outputMemory: Map<MemoryDescriptor, VersionedMemory>
        ): Bool_ {
            val inputMemoryArrays = memoryDescriptors.map { inputMemory.getValue(it) }.map { it.memory.inner }
            val outputMemoryArrays = memoryDescriptors.map { outputMemory.getValue(it) }.map { it.memory.inner }
            val axiomSources = listOf(owner, returnValue) + arguments + inputMemoryArrays + outputMemoryArrays
            val axioms = axiomSources.map { it.axiomExpr() }
                    .reduceOrNull { acc, ax -> acc.withAxiom(ax) } ?: ef.makeTrue()
            return apply(
                    ef,
                    owner.expr(), arguments.expr(), returnValue.expr(),
                    inputMemoryArrays.arrayExpr(), outputMemoryArrays.arrayExpr()
            ).withAxiom(axioms)
        }

        fun apply(
                ef: Z3ExprFactory,
                owner: Expr, arguments: List<Expr>, returnValue: Expr,
                inputMemory: List<Expr>, outputMemory: List<Expr>
        ): Bool_ {
            val inputs = listOf(owner) + arguments + inputMemory
            val outputs = listOf(returnValue) + outputMemory
            val predicateApp = ef.ctx.mkApp(decl, *(inputs + outputs).toTypedArray())
            return Bool_(ef.ctx, predicateApp)
        }

        fun argumentDeclarations(
                owner: Declaration, arguments: List<Declaration>, inputMemory: List<Declaration>
        ): ArgumentDeclarations {
            return ArgumentDeclarations.createFromOrdered(listOf(owner) + arguments + inputMemory)
        }

        private fun Dynamic_.expr() = expr
        private fun List<Dynamic_>.expr() = map { it.expr() }
        private fun Array_<Dynamic_, Ptr_>.arrayExpr() = expr
        private fun List<Array_<Dynamic_, Ptr_>>.arrayExpr() = map { it.arrayExpr() }
    }

    data class RootPredicate(val predicate: Bool_, val arguments: ArgumentDeclarations)

    private fun KexType.z3Sort(ef: Z3ExprFactory) = Dynamic_.getStaticSort(ef.ctx, Z3ExprFactory.getType(this))
    private fun MemoryDescriptor.z3Sort(ctx: Z3Context): Sort {
        val memory = ctx.getInitials()[this] ?: error("No memory for descriptor: $this")
        return memory.memory.inner.expr.sort
    }

    fun buildRootPredicateApp(declarationTracker: DeclarationTracker, ef: Z3ExprFactory, ctx: Z3Context): RootPredicate {
        val z3RecursionPredicate = buildPredicate(ef, ctx)
        val allInputMemory = inputMemoryDeclarations(declarationTracker)
        val inputMemory = z3RecursionPredicate.memoryDescriptors.map {
            allInputMemory[it] ?: error("No memory for descriptor $it")
        }
        val owner = declarationTracker.findThis()
        val arguments = declarationTracker.arguments()
        val predicateArgDeclarations = z3RecursionPredicate.argumentDeclarations(owner, arguments, inputMemory)
        val outputMemory = outputMemory(ctx)
        val returnValue = returnValue(ef, z3RecursionPredicate.returnValueType)

        val ownerExpr = owner.expr
        val argumentExprs = arguments.map { it.expr }
        val inputMemoryExprs = inputMemory.map { it.expr }
        val returnValueExpr = returnValue.expr
        val outputMemoryExprs = outputMemory.map { it.expr }
        val predicateApp = z3RecursionPredicate.apply(ef, ownerExpr, argumentExprs, returnValueExpr, inputMemoryExprs, outputMemoryExprs)

        val axiom = outputMemory.fold(returnValue.axiomExpr()) { acc, mem -> acc.withAxiom(mem.axiomExpr()) }
        return RootPredicate(predicateApp.withAxiom(axiom), predicateArgDeclarations)
    }

    private fun inputMemoryDeclarations(
            tracker: DeclarationTracker,
    ): Map<MemoryDescriptor, Declaration.Memory> {
        val memoryDeclarations = tracker.memories(memoryVersionInfo.initial)
        check(memoryVersionInfo.initial.size == memoryDeclarations.size) { "Missed declarations" }
        return memoryDeclarations
    }

    private fun outputMemory(
            ctx: Z3Context,
    ) = memoryVersionInfo.final
            .map { (descriptor, version) -> ctx.getMemory(descriptor, version) }
            .map { it.memory.inner }

    private fun returnValue(ef: Z3ExprFactory, type: KexType) =
            ef.getVarByTypeAndName(type, "recursion_return_value_stub")

    private fun DeclarationTracker.findThis() = declarations.filterIsInstance<Declaration.This>().first()
    private fun DeclarationTracker.arguments() = declarations.filterIsInstance<Declaration.Argument>().sortedBy { it.index }
    private fun DeclarationTracker.memories(versions: Map<MemoryDescriptor, MemoryVersion>) = declarations
            .filterIsInstance<Declaration.Memory>()
            .filter { it.version == versions[it.descriptor] }
            .associateBy { it.descriptor }

}

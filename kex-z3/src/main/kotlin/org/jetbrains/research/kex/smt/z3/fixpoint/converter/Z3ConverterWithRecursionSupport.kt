package org.jetbrains.research.kex.smt.z3.fixpoint.converter

import com.microsoft.z3.FuncDecl
import com.microsoft.z3.Sort
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.smt.z3.fixpoint.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.Declaration
import org.jetbrains.research.kex.state.CallApproximationState
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.memory.MemoryVersionInfo
import org.jetbrains.research.kex.state.memory.MemoryVersionType
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
        val predicateApp = z3RecursionPredicate.apply(ef, callArguments.first(), callArguments.drop(1), returnValue, memoryBeforeCall, memoryAfterCall)
        val callAxiom = callArguments.map { it.axiomExpr() }
                .fold(callInfo.result) { res, ax -> res.withAxiom(ax) }
        return predicateApp and callAxiom
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
        val returnSort = callPrototype.method.returnType.kexType.z3Sort(ef)
        val memoryDescriptors = memoryVersionInfo.allMemoryVersions.keys.toList()
        val memorySorts = memoryDescriptors.map { it.z3Sort(ctx) }
        val allArgumentSorts = listOf(ownerSort) + argumentSorts + memorySorts + listOf(returnSort) + memorySorts
        val funDecl = ef.ctx.mkFuncDecl(recursionPredicate.name, allArgumentSorts.toTypedArray(), ef.ctx.mkBoolSort())
        z3RecursionPredicateUnsafe = Predicate(funDecl, memoryDescriptors)
        return z3RecursionPredicateUnsafe
    }

    data class Predicate(val decl: FuncDecl, val memoryDescriptors: List<MemoryDescriptor>) {
        fun apply(
                ef: Z3ExprFactory,
                owner: Dynamic_, arguments: List<Dynamic_>, returnValue: Dynamic_,
                inputMemory: Map<MemoryDescriptor, VersionedMemory>, outputMemory: Map<MemoryDescriptor, VersionedMemory>
        ): Bool_ {
            val inputMemoryArrays = memoryDescriptors.map { inputMemory.getValue(it) }.map { it.memory.inner }
            val outputMemoryArrays = memoryDescriptors.map { outputMemory.getValue(it) }.map { it.memory.inner }
            return apply(ef, owner, arguments, returnValue, inputMemoryArrays, outputMemoryArrays)
        }

        private fun apply(
                ef: Z3ExprFactory,
                owner: Dynamic_, arguments: List<Dynamic_>, returnValue: Dynamic_,
                inputMemory: List<Array_<Dynamic_, Ptr_>>, outputMemory: List<Array_<Dynamic_, Ptr_>>
        ): Bool_ {
            val inputs = listOf(owner.expr) + arguments.map { it.expr } + inputMemory.map { it.expr }
            val outputs = listOf(returnValue.expr) + outputMemory.map { it.expr }
            val predicateApp = ef.ctx.mkApp(decl, *(inputs + outputs).toTypedArray())
            return Bool_(ef.ctx, predicateApp)
        }
    }

    private fun KexType.z3Sort(ef: Z3ExprFactory) = Dynamic_.getStaticSort(ef.ctx, Z3ExprFactory.getType(this))
    private fun MemoryDescriptor.z3Sort(ctx: Z3Context): Sort {
        val memory = ctx.getInitials()[this] ?: error("No memory for descriptor: $this")
        return memory.memory.inner.expr.sort
    }

    fun buildRootPredicateApp(declaration: List<Declaration>, ef: Z3ExprFactory, ctx: Z3Context) {
        val finalVersion = memoryVersionInfo.allMemoryVersions.values.flatMap { it.values }
                .filter { it.type == MemoryVersionType.NEW || it.type == MemoryVersionType.INITIAL }
                .map { it.version }
                .maxOrNull() ?: 0
        val afterFinalVersion = finalVersion + 1
        val afterVersions = memoryVersionInfo.final.mapValues { (_, currVersion) -> currVersion.resetToVersion(afterFinalVersion) }

    }

    private fun List<Declaration>.findThis() = filterIsInstance<Declaration.This>().first()
    private fun List<Declaration>.findArgument(idx: Int) = filterIsInstance<Declaration.Argument>()
            .first { it.index == idx }

    private fun List<Declaration>.findMemory(descriptor: MemoryDescriptor, version: MemoryVersion) = filterIsInstance<Declaration.Memory>()
            .first { it.descriptor == descriptor && it.version == version }

}

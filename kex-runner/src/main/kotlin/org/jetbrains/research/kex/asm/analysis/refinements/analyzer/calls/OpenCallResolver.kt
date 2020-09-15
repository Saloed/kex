package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import org.jetbrains.research.kex.asm.analysis.refinements.MethodApproximationManager
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.MethodImplementationMerge
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.MethodImplementations
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.ktype.KexBool
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.TermDependency
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.chain
import org.jetbrains.research.kex.state.memory.MemoryAccessScope
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.InstanceOfTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.util.VariableGenerator
import org.jetbrains.research.kfg.ir.Method

class OpenCallResolver(
        resolvingCall: CallPredicate,
        currentCallContext: CallContext,
        methodAnalyzer: MethodAnalyzer,
        approximationManager: MethodApproximationManager
) : SingleCallResolver(resolvingCall, currentCallContext, methodAnalyzer, approximationManager) {
    override fun resolve(
            state: PredicateStateWithPath,
            dependencies: List<TermDependency>, pathVariables: Set<Term>,
            tmpVariables: Set<Term>
    ): RecoveredModel {
        val implementations = MethodImplementations(methodAnalyzer.cm, methodAnalyzer.refinementsManager).collectImplementations(resolvingMethod)
        val preconditions = implementations.associateWith { method ->
            val callOwner = resolvingCallTerm.owner
            val newCall = CallTerm(
                    resolvingCallTerm.type, callOwner,
                    method, resolvingCallTerm.instruction,
                    resolvingCallTerm.arguments, resolvingCallTerm.memoryVersion
            )
            val newCallPredicate = CallPredicate(resolvingCall.lhvUnsafe, newCall, resolvingCall.type, resolvingCall.location)
            val newDependencies = dependencies.map {
                when (it) {
                    is TermDependency.CallResultDependency -> TermDependency.CallResultDependency(it.term, it.callIdx, newCallPredicate)
                    is TermDependency.MemoryDependency -> TermDependency.MemoryDependency(it.memoryAccess, it.callIdx, newCallPredicate)
                }
            }
            val typeCheckPV = currentCallContext.variableGenerator.generatorFor("type_check").createVar(KexBool())
            val resolver = ImplementationResolver(method, newCallPredicate, typeCheckPV)
            resolver.resolve(state, newDependencies, pathVariables, tmpVariables)
        }
        val preconditionStates = preconditions.mapValues { (_, model) -> model.finalStateOrException() }.map { it.value to it.key }
        val preconditionMerger = OpenCallPreconditionMerge(preconditions, currentCallContext.parent.scope, resolvingCall.memoryVersion, resolvingMethod)
        val mergedState = preconditionMerger.mergeImplementations(preconditionStates)
        val mergedTmpVariables = preconditionMerger.tmpGenerator.generatedVariables().toSet()
        val mergedPathVariables = preconditionMerger.pathGenerator.generatedVariables().toSet()
        return RecoveredModel(mergedState, emptySet(), mergedPathVariables, mergedTmpVariables)
    }

    inner class ImplementationResolver(
            val method: Method,
            callPredicate: CallPredicate,
            val typeCheckPV: Term
    ) : InlineCallResolver(callPredicate, currentCallContext, methodAnalyzer, approximationManager) {
        override fun inliningMethodState(callPredicate: CallPredicate): PredicateState {
            val methodState =  super.inliningMethodState(callPredicate)
            val typeCondition = basic {
                state {
                    typeCheckPV equality (callPredicate.callTerm.owner `is` method.`class`.kexType)
                }
            }
            return chain(typeCondition, methodState)
        }
    }

    class OpenCallPreconditionMerge(
            val preconditions: Map<Method, RecoveredModel>,
            val scope: MemoryAccessScope,
            val version: MemoryVersion,
            method: Method
    ) : MethodImplementationMerge(method) {
        override val baseGenerator: VariableGenerator = VariableGenerator("resolved_impls")
        override fun mapUnmappedTerm(method: Method, term: Term): Term? {
            val model = preconditions[method] ?: error("Method not found in preconditions")
            return when (term) {
                in model.tmpVariables -> null
                in model.pathVariables -> null
                else -> term
            }
        }

        override fun createInstanceOf(term: Term, type: KexType) =
                (super.createInstanceOf(term, type) as InstanceOfTerm).withScopeInfo(scope).withMemoryVersion(version)
    }
}

package org.jetbrains.research.kex.refinements.analyzer.calls

import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.refinements.MethodApproximationManager
import org.jetbrains.research.kex.refinements.analyzer.utils.MethodImplementationMerge
import org.jetbrains.research.kex.refinements.analyzer.utils.MethodImplementations
import org.jetbrains.research.kex.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.model.TermDependency
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.chain
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
        log.debug("Resolve open call: $resolvingCall")
        val implementations = MethodImplementations(methodAnalyzer.cm, methodAnalyzer.refinementsManager).collectImplementations(resolvingMethod)
        val preconditions = implementations.associateWith { method ->
            analyzeImplementation(method, dependencies, state, pathVariables, tmpVariables)
        }
        val preconditionStates = preconditions.mapValues { (_, model) -> model.finalStateOrException() }.map { it.value to it.key }
        val preconditionMerger = OpenCallPreconditionMerge(preconditions)
        val mergedState = preconditionMerger.mergeImplementations(preconditionStates)
        val mergedTmpVariables = preconditionMerger.tmpGenerator.generatedVariables().toSet()
        val mergedPathVariables = preconditionMerger.pathGenerator.generatedVariables().toSet()
        return RecoveredModel(mergedState, emptySet(), mergedPathVariables, mergedTmpVariables)
    }

    private fun analyzeImplementation(
            method: Method,
            dependencies: List<TermDependency>,
            state: PredicateStateWithPath,
            pathVariables: Set<Term>,
            tmpVariables: Set<Term>
    ): RecoveredModel {
        log.debug("Resolve open call implementation: $method")
        if (!checkOwnerTypes(method, resolvingCallTerm.owner)) {
            return RecoveredModel.error()
        }
        val newOwner = currentCallContext.variableGenerator.createNestedGenerator("call_owner").unique().createUniqueVar(method.klass.kexType)
        val newCall = CallTerm(
                resolvingCallTerm.type, newOwner,
                method, resolvingCallTerm.instruction,
                resolvingCallTerm.arguments, resolvingCallTerm.memoryVersion
        )
        val newCallPredicate = CallPredicate(resolvingCall.lhvUnsafe, newCall, resolvingCall.type, resolvingCall.location)
        val newDependencies = dependencies.map { it.updateCallPredicate(newCallPredicate) }
        val resolver = ImplementationResolver(method, newCallPredicate)
        val resolvedPreconditions = resolver.resolve(state, newDependencies, pathVariables, tmpVariables)
        return resolvedPreconditions.copy(state = updateCallOwner(resolvedPreconditions.state, newOwner, resolvingCallTerm.owner))
    }

    private fun updateCallOwner(stateWithPath: PredicateStateWithPath, ownerPlaceholder: Term, owner: Term): PredicateStateWithPath {
        val ownerBinding = basic {
            state { ownerPlaceholder equality owner }
        }
        return stateWithPath.copy(state = chain(ownerBinding, stateWithPath.state))
    }

    private fun checkOwnerTypes(method: Method, owner: Term): Boolean {
        val ownerType = (owner.type as KexClass).getKfgClass(methodAnalyzer.cm.type)
        return method.klass.isInheritorOf(ownerType)
    }

    inner class ImplementationResolver(
            val method: Method,
            callPredicate: CallPredicate
    ) : InlineCallResolver(callPredicate, currentCallContext, methodAnalyzer, approximationManager)

    inner class OpenCallPreconditionMerge(
            val preconditions: Map<Method, RecoveredModel>
    ) : MethodImplementationMerge(resolvingMethod) {
        override val owner: Term
            get() = resolvingCallTerm.owner
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
                (super.createInstanceOf(term, type) as InstanceOfTerm)
                        .withScopeInfo(currentCallContext.parent.scope)
                        .withMemoryVersion(resolvingCall.memoryVersion)
    }
}

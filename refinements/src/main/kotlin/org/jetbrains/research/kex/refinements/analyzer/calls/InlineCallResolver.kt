package org.jetbrains.research.kex.refinements.analyzer.calls

import org.jetbrains.research.kex.refinements.MethodApproximationManager
import org.jetbrains.research.kex.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.refinements.solver.CallResolveSolverQuery
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.fixpoint.model.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.model.TermDependency
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.FieldTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kex.state.transformer.TermRemapper
import org.jetbrains.research.kex.state.transformer.VariableCollector
import org.jetbrains.research.kex.state.transformer.collectVariables
import kotlin.math.absoluteValue

open class InlineCallResolver(
        resolvingCall: CallPredicate,
        currentCallContext: CallContext,
        methodAnalyzer: MethodAnalyzer,
        approximationManager: MethodApproximationManager
) : SingleCallResolver(resolvingCall, currentCallContext, methodAnalyzer, approximationManager) {

    override fun resolve(
            state: PredicateStateWithPath,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>,
            tmpVariables: Set<Term>
    ): RecoveredModel {
        val callArguments = collectArguments(state, dependencies, pathVariables, tmpVariables)
        return analyzeMethodState(state, dependencies, callArguments)
    }

    private fun analyzeMethodState(
            state: PredicateStateWithPath,
            dependencies: List<TermDependency>,
            callArguments: CallArguments
    ): RecoveredModel {
        val preparedMethod = prepareInliningMethod(dependencies)
        val result = analyzeWithMemory(preparedMethod, state, callArguments)
        val preconditionPathVariables = collectVariables(preparedMethod.callPreconditions.path)
//        val resultState = PredicateStateWithPath.chain(listOf(preparedMethod.callPreconditions, result.state))
        val resultState = result.state
        return result.copy(state = resultState, pathVariables = result.pathVariables + preconditionPathVariables)
    }

    private fun analyzeWithMemory(
            preparedMethod: PreparedInlinedCall,
            state: PredicateStateWithPath,
            callArguments: CallArguments
    ): RecoveredModel {
        val methodStateToAnalyze = updateMemoryVersionsAfterInlining(state.state, preparedMethod)
        val result = analyzeWithMappedArguments(methodStateToAnalyze.state, state.path, methodStateToAnalyze.memoryVersionInfo, callArguments)
        val resultWithRestoredMemory = restoreStateMemory(result.state.state, methodStateToAnalyze.memoryMapping)
        val resultState = PredicateStateWithPath(resultWithRestoredMemory, result.state.path)
        return result.copy(state = resultState)
    }

    private fun analyzeWithMappedArguments(
            state: PredicateState,
            query: PredicateState,
            memoryVersionInfo: MemoryVersionInfo,
            callArguments: CallArguments
    ): RecoveredModel {
        val mappedState = callArguments.forwardMapper.apply(state)
        val result = analyzeState(mappedState, query, memoryVersionInfo, callArguments.arguments)
        val resultState = callArguments.backwardMapper.apply(result.state.state)
        val resultStateWithPath = PredicateStateWithPath(resultState, result.state.path)
        return result.copy(state = resultStateWithPath)
    }

    private fun analyzeState(
            state: PredicateState,
            query: PredicateState,
            memoryVersionInfo: MemoryVersionInfo,
            arguments: List<Term>
    ): RecoveredModel {
        val solverArgument = CallResolveSolverQuery(state, query, query.not(), arguments, emptySet(), memoryVersionInfo, 0)
        val result = analyzeState(solverArgument)
        return result.copy(dependencies = emptySet())
    }

    private fun analyzeState(argument: CallResolveSolverQuery): RecoveredModel {
        val resolver = CallResolver(methodAnalyzer, approximationManager, currentCallContext)
        return resolver.callResolutionLoop(argument.wrap()).first()
    }

    private fun updateMemoryVersionsAfterInlining(
            state: PredicateState,
            preparedMethod: PreparedInlinedCall
    ): InlinedCallInfo {
        check(resolvingCall.memoryVersion.type == MemoryVersionType.NEW) { "Call memory must be NEW" }
        val (preparedState, mapping) = MemoryUtils.newAsSeparateInitialVersions(state).let { it.first to it.second.toMutableMap() }
        val descriptorMapping = preparedMethod.finalMemory.keys.associateBy({ it }) {
            mapping.getOrPut(it.withScope(currentCallContext.parent.scope) to resolvingCall.memoryVersion) {
                it.withScope(currentCallContext.scope) to MemoryVersion.initial()
            }.first.scopeInfo
        }
        val mappedFinals = preparedMethod.finalMemory.mapKeys { (descriptor, _) ->
            val scope = descriptorMapping[descriptor] ?: error("No scope mapped")
            descriptor.withScope(scope)
        }
        val replacement = mappedFinals.mapValues { (_, final) -> MemoryVersion.initial() to final }
        val scopedMethodState = ScopeInfoMapper(descriptorMapping).apply(preparedMethod.state)
        val newState = MemoryUtils.replaceMemoryVersion(preparedState, replacement)
        val resultState = ChainState(scopedMethodState, newState)
        val memoryVersionInfo = MemoryVersionInfoCollector.collect(resultState)
        MemoryUtils.verify(resultState, memoryVersionInfo)
        return InlinedCallInfo(resultState, mapping, memoryVersionInfo)
    }

    internal class ScopeInfoMapper(val mapping: Map<MemoryDescriptor, MemoryAccessScope>) : MemoryVersionTransformer {
        override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
            val newScope = mapping[element.descriptor()]
                    ?: error("No scope mapped for element ${element.descriptor()}")
            return element.withScopeInfo(newScope)
        }
    }

    private fun restoreStateMemory(state: PredicateState, memoryMapping: MemoryMappingType): PredicateState {
        val backwardMapping = memoryMapping.entries.associateBy({ it.value }, { it.key })
        return MemoryMapper(backwardMapping).apply(state)
    }

    internal inner class MemoryMapper(val mapping: MemoryMappingType) : MemoryVersionTransformer {
        @Suppress("UNCHECKED_CAST")
        override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
            val currentDescriptor = element.descriptor()
            val elementKey = currentDescriptor to element.memoryVersion
            val (newDescriptor, newVersion) = mapping[elementKey]
                    ?: maybeNewMemoryDescriptor(currentDescriptor, element.memoryVersion)
                    ?: return super.transformMemoryVersion(element)
            check(currentDescriptor.run {
                memoryType == newDescriptor.memoryType
                        && memoryName == newDescriptor.memoryName
                        && memorySpace == newDescriptor.memorySpace
            }) { "This mapper can change only scope info" }
            var result = element.withScopeInfo(newDescriptor.scopeInfo)
            result as MemoryAccess<T>
            result = result.withMemoryVersion(newVersion)
            return result
        }

        private fun maybeNewMemoryDescriptor(descriptor: MemoryDescriptor, version: MemoryVersion): Pair<MemoryDescriptor, MemoryVersion>? {
            if (descriptor.scopeInfo != currentCallContext.scope) return null
            if (version != MemoryVersion.initial()) {
                error("Non mapped non initial")
            }
            val newDescriptor = descriptor.withScope(currentCallContext.parent.scope)
            return newDescriptor to currentCallContext.version
        }
    }

    private fun prepareInliningMethod(dependencies: List<TermDependency>): PreparedInlinedCall {
        val retvalPlaceholder = term { value(resolvingMethod.returnType.kexType, "retval_${resolvingCallTerm.hashCode().absoluteValue}") }
        val predicateToInline = CallPredicate(retvalPlaceholder, resolvingCallTerm)
        val inliner = CallInliner(methodAnalyzer.cm, methodAnalyzer.psa, methodAnalyzer,
                forceDeepInline = true, forceMethodInlining = resolvingMethod)
        val unconditionedMethodState = inliner.apply(predicateToInline.wrap())
        val noErrorCondition = createSuccessExecutionCondition(predicateToInline, inliner)
        val methodState = chain(noErrorCondition.path, unconditionedMethodState)
        check(predicateToInline !in PredicateCollector.collectIsInstance<CallPredicate>(methodState)) { "Call was not inlined" }
        val retvalBindings = basic {
            dependencies.filterIsInstance<TermDependency.CallResultDependency>().forEach { dependency ->
                predicate(PredicateType.State()) { dependency.term equality retvalPlaceholder }
            }
        }
        val methodStateForInlining = chain(methodState, retvalBindings)
        val memoryVersioner = MemoryVersioner()
        val versionedMethodState = memoryVersioner.apply(methodStateForInlining)
        val finalVersions = memoryVersioner.memoryInfo().final
        return PreparedInlinedCall(versionedMethodState, noErrorCondition, finalVersions)
    }

    private fun createSuccessExecutionCondition(call: CallPredicate, inliner: CallInliner): PredicateStateWithPath {
        val noErrorCondition = inliner.callPathConditions[call]?.noErrorCondition() ?: emptyState()
        val state = inliner.callPathConditionState.apply()
        return PredicateStateWithPath(state, noErrorCondition)
    }

    private fun collectArguments(
            state: PredicateStateWithPath,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>,
            tmpVariables: Set<Term>
    ): CallArguments {
        val callArguments = VariableCollector().apply { transform(resolvingCallTerm) }.variables
        val callResultDependentTerms = dependencies.filterIsInstance<TermDependency.CallResultDependency>().map { it.term }.toSet()
        val memoryDependency = dependencies.filterIsInstance<TermDependency.MemoryDependency>().map { it.memoryAccess }.toSet()
        val stateArguments = collectVariables(state.state).asSequence()
                .filterNot { it is FieldTerm }
                .filterNot { it in callResultDependentTerms }
                .filterNot { it is MemoryAccess<*> && it in memoryDependency }
                .filterNot { it in pathVariables }
                .filterNot { it in tmpVariables }
                .toList()
        val argumentsMapping = (callArguments + stateArguments).distinct().mapIndexed { i, term -> term to term { arg(term.type, i) } }.toMap()
        val backwardMapping = argumentsMapping.entries.associateBy({ it.value }, { it.key })
        val argumentTerms = backwardMapping.keys.toList()
        return CallArguments(argumentTerms, TermRemapper(argumentsMapping), TermRemapper(backwardMapping))
    }

    data class InlinedCallInfo(
            val state: PredicateState,
            val memoryMapping: MemoryMappingType,
            val memoryVersionInfo: MemoryVersionInfo
    )

    data class PreparedInlinedCall(
            val state: PredicateState,
            val callPreconditions: PredicateStateWithPath,
            val finalMemory: Map<MemoryDescriptor, MemoryVersion>
    )

    data class CallArguments(
            val arguments: List<Term>,
            val forwardMapper: TermRemapper,
            val backwardMapper: TermRemapper
    )
}

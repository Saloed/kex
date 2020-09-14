package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import org.jetbrains.research.kex.asm.analysis.refinements.MethodApproximationManager
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.solver.CallResolveSolverQuery
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.TermDependency
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

class InlineCallResolver(
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
        val (arguments, forwardMapping, backwardMapping) = collectArguments(state, dependencies, pathVariables, tmpVariables)
        val methodWithInlinedDependencies = inlineCallDependencies(state.state, dependencies)
        val stateToAnalyze = forwardMapping.apply(methodWithInlinedDependencies.state)
        val normalExecutionPath = forwardMapping.apply(methodWithInlinedDependencies.normalExecutionPath)
        val positive = chain(state.path, normalExecutionPath)
        val negative = choice(state.path.not(), normalExecutionPath.not())
        val argument = CallResolveSolverQuery(stateToAnalyze, positive, negative, arguments, emptySet(),
                methodWithInlinedDependencies.memoryVersionInfo, 0)
        val resultModel = analyzeState(argument)
        val resultState = backwardMapping.apply(resultModel.state.state)
        val resultWithRestoredMemory = restoreStateMemory(resultState, methodWithInlinedDependencies.memoryMapping)
        val resultStateWithPath = PredicateStateWithPath(resultWithRestoredMemory, resultModel.state.path)
        return RecoveredModel(resultStateWithPath, emptySet(), resultModel.pathVariables, resultModel.tmpVariables)
    }

    private fun analyzeState(argument: CallResolveSolverQuery): RecoveredModel {
        val resolver = CallResolver(methodAnalyzer, approximationManager, currentCallContext)
        return resolver.callResolutionLoop(argument.wrap()).first()
    }

    private data class InlinedCallInfo(
            val state: PredicateState,
            val normalExecutionPath: PredicateState,
            val memoryMapping: MemoryMappingType,
            val memoryVersionInfo: MemoryVersionInfo
    )

    private data class PreparedInlinedCall(
            val state: PredicateState,
            val normalExecutionPath: PredicateState,
            val finalMemory: Map<MemoryDescriptor, MemoryVersion>
    )

    private fun inlineCallDependencies(
            state: PredicateState,
            dependencies: List<TermDependency>
    ): InlinedCallInfo {
        val preparedMethod = prepareInliningMethod(dependencies)
        check(resolvingCall.memoryVersion.type == MemoryVersionType.NEW) { "Call memory must be NEW" }
        return updateMemoryVersionsAfterInlining(state, preparedMethod)
    }

    private fun updateMemoryVersionsAfterInlining(
            state: PredicateState,
            preparedMethod: PreparedInlinedCall
    ): InlinedCallInfo {
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
        return InlinedCallInfo(resultState, preparedMethod.normalExecutionPath, mapping, memoryVersionInfo)
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
        val retvalPlaceholder = term { value(resolvingMethod.returnType.kexType, "retval_${resolvingCallTerm.hashCode()}") }
        val predicateToInline = CallPredicate(retvalPlaceholder, resolvingCallTerm)
        val inliner = CallInliner(methodAnalyzer.cm, methodAnalyzer.psa, methodAnalyzer, forceDeepInline = true, forceMethodInlining = resolvingMethod)
        val methodState = inliner.apply(predicateToInline.wrap())
        check(predicateToInline !in PredicateCollector.collectIsInstance<CallPredicate>(methodState)) { "Call was not inlined" }
        val retvalBindings = basic {
            dependencies.filterIsInstance<TermDependency.CallResultDependency>().forEach { dependency ->
                predicate(PredicateType.State()) { dependency.term equality retvalPlaceholder }
            }
        }
        val normalExecutionConditions = inliner.callPathConditions[predicateToInline]?.noErrorCondition()
                ?: emptyState()
        val methodStateForInlining = chain(methodState, retvalBindings)
        val memoryVersioner = MemoryVersioner()
        val versionedMethodState = memoryVersioner.apply(methodStateForInlining)
        val finalVersions = memoryVersioner.memoryInfo().final
        return PreparedInlinedCall(versionedMethodState, normalExecutionConditions, finalVersions)
    }

    private fun collectArguments(
            state: PredicateStateWithPath,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>,
            tmpVariables: Set<Term>
    ): Triple<List<Term>, TermRemapper, TermRemapper> {
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
        return Triple(argumentTerms, TermRemapper(argumentsMapping), TermRemapper(backwardMapping))
    }
}

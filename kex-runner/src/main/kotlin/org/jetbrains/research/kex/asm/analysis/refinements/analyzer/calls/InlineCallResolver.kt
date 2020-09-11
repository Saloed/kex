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
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.FieldTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kex.state.transformer.TermRemapper
import org.jetbrains.research.kex.state.transformer.VariableCollector
import org.jetbrains.research.kex.state.transformer.collectVariables

class InlineCallResolver(
        currentCallContext: CallContext,
        methodAnalyzer: MethodAnalyzer,
        approximationManager: MethodApproximationManager
) : SingleCallResolver(currentCallContext, methodAnalyzer, approximationManager) {

    override fun resolve(
            state: PredicateStateWithPath,
            call: CallPredicate,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>, tmpVariables: Set<Term>
    ): RecoveredModel {
        val (arguments, forwardMapping, backwardMapping) = collectArguments(state, call, dependencies, pathVariables, tmpVariables)
        val (stateWithDependencyInlined, memoryMapping, memoryVersionInfo) = inlineCallDependencies(state.state, call, dependencies)
        val stateToAnalyze = forwardMapping.apply(stateWithDependencyInlined)
        val positive = state.path
        val negative = state.negate().path
        val argument = CallResolveSolverQuery(stateToAnalyze, positive, negative, arguments, emptySet(), memoryVersionInfo, 0)
        val resultModel = analyzeState(argument)
        val resultState = backwardMapping.apply(resultModel.state.state)
        val resultWithRestoredMemory = restoreStateMemory(resultState, memoryMapping)
        val resultStateWithPath = PredicateStateWithPath(resultWithRestoredMemory, resultModel.state.path)
        return RecoveredModel(resultStateWithPath, emptySet(), resultModel.pathVariables, resultModel.tmpVariables)
    }


    private fun analyzeState(argument: CallResolveSolverQuery): RecoveredModel {
        val resolver = CallResolver(methodAnalyzer, approximationManager, currentCallContext)
        return resolver.callResolutionLoop(argument.wrap()).first()
    }


    private fun inlineCallDependencies(
            state: PredicateState,
            callPredicate: CallPredicate,
            dependencies: List<TermDependency>
    ): Triple<PredicateState, MemoryMappingType, MemoryVersionInfo> {
        val (methodState, finalVersions) = prepareInliningMethod(callPredicate, dependencies)
        val callMemoryVersion = callPredicate.memoryVersion
        check(callMemoryVersion.type == MemoryVersionType.NEW) { "Call memory must be NEW" }
        return updateMemoryVersionsAfterInlining(state, finalVersions, callMemoryVersion, methodState)
    }

    private fun updateMemoryVersionsAfterInlining(
            state: PredicateState,
            finalVersions: Map<MemoryDescriptor, MemoryVersion>,
            callMemoryVersion: MemoryVersion,
            methodState: PredicateState
    ): Triple<ChainState, MutableMap<Pair<MemoryDescriptor, MemoryVersion>, Pair<MemoryDescriptor, MemoryVersion>>, MemoryVersionInfo> {
        val (preparedState, mapping) = MemoryUtils.newAsSeparateInitialVersions(state).let { it.first to it.second.toMutableMap() }
        val descriptorMapping = finalVersions.keys.associateBy({ it }) {
            mapping.getOrPut(it.withScope(currentCallContext.parent.scope) to callMemoryVersion) {
                it.withScope(currentCallContext.scope) to MemoryVersion.initial()
            }.first.scopeInfo
        }
        val mappedFinals = finalVersions.mapKeys { (descriptor, _) ->
            val scope = descriptorMapping[descriptor] ?: error("No scope mapped")
            descriptor.withScope(scope)
        }
        val replacement = mappedFinals.mapValues { (_, final) -> MemoryVersion.initial() to final }
        val scopedMethodState = ScopeInfoMapper(descriptorMapping).apply(methodState)
        val newState = MemoryUtils.replaceMemoryVersion(preparedState, replacement)
        val resultState = ChainState(scopedMethodState, newState)
        val memoryVersionInfo = MemoryVersionInfoCollector.collect(resultState)
        MemoryUtils.verify(resultState, memoryVersionInfo)
        return Triple(resultState, mapping, memoryVersionInfo)
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

    private fun prepareInliningMethod(callPredicate: CallPredicate, dependencies: List<TermDependency>): Pair<PredicateState, Map<MemoryDescriptor, MemoryVersion>> {
        val call = callPredicate.call as CallTerm
        val retvalPlaceholder = term { value(call.method.returnType.kexType, "retval_${call.hashCode()}") }
        val predicateToInline = CallPredicate(retvalPlaceholder, call)
        val inliner = CallInliner(methodAnalyzer.cm, methodAnalyzer.psa, methodAnalyzer, forceDeepInline = true, forceMethodInlining = call.method)
        val methodState = inliner.apply(predicateToInline.wrap())
        check(predicateToInline !in PredicateCollector.collectIsInstance<CallPredicate>(methodState)) { "Call was not inlined" }
        val retvalBindings = basic {
            dependencies.filterIsInstance<TermDependency.CallResultDependency>().forEach { dependency ->
                predicate(PredicateType.State()) { dependency.term equality retvalPlaceholder }
            }
        }
        val normalExecutionConditions = inliner.callPathConditions[predicateToInline]?.noErrorCondition() ?: emptyState()
        val methodStateForInlining = chain(listOf(methodState, retvalBindings, normalExecutionConditions))
        val memoryVersioner = MemoryVersioner()
        val versionedMethodState = memoryVersioner.apply(methodStateForInlining)
        val finalVersions = memoryVersioner.memoryInfo().final
        return versionedMethodState to finalVersions
    }

    private fun collectArguments(state: PredicateStateWithPath, call: CallPredicate, dependencies: List<TermDependency>, pathVariables: Set<Term>, tmpVariables: Set<Term>): Triple<List<Term>, TermRemapper, TermRemapper> {
        val callArguments = VariableCollector().apply { transform(call.call) }.variables
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

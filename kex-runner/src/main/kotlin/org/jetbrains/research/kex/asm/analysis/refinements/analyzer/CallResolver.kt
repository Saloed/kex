package org.jetbrains.research.kex.asm.analysis.refinements.analyzer

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.refinements.MethodApproximationManager
import org.jetbrains.research.kex.asm.analysis.refinements.MethodUnderApproximation
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method.MethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.solver.CallResolveSolverQuery
import org.jetbrains.research.kex.asm.analysis.refinements.solver.FixpointSolver
import org.jetbrains.research.kex.asm.analysis.refinements.solver.SolverQuery
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kex.smt.z3.fixpoint.TermDependency
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.memory.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateBuilder
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kex.util.VariableGenerator
import org.jetbrains.research.kfg.ir.Method
import kotlin.math.absoluteValue

class CallResolver(
        val methodAnalyzer: MethodAnalyzer,
        val approximationManager: MethodApproximationManager,
        private val parentResolver: CallResolver? = null
) {
    private val variableGenerator: VariableGenerator
        get() = parentResolver?.variableGenerator?.createNestedGenerator("x")
                ?: VariableGenerator("cr")

    private var currentCallContext: CallContext? = null
    private val baseCallContext: CallContext
        get() = parentResolver?.currentCallContext ?: CallContext.ROOT

    inline fun <reified T : SolverQuery<T, List<RecoveredModel>>> callResolutionLoop(query: T): List<RecoveredModel> {
        while (true) {
            log.debug("Enter ${query.iteration} call resolution loop for ${methodAnalyzer.method}")
            val processed = query.updateIteration { it.inc() }
                    .transform { approximationManager.extendWithUnderApproximations(it) }
                    .updateIgnoredCalls { ignoreCalls(query, it) }
                    .acceptMemoryCorrector { ps, versionInfo ->
                        approximationManager.correctMemoryAfterApproximation(ps, versionInfo)
                    }
                    .run(FixpointSolver(methodAnalyzer.cm))
            when {
                processed.all { it.isFinal } -> return processed
                else -> processed.forEach { resolveCalls(it) }
            }
        }
    }

    fun <T : SolverQuery<T, List<RecoveredModel>>> ignoreCalls(query: T, ignored: Set<CallPredicate>): Set<CallPredicate> {
        val callCollector = PredicateCollector { it is CallPredicate }
        query.transform { callCollector.transform(it); it }
        val allCalls = callCollector.predicates.filterIsInstance<CallPredicate>().toSet()
        val callsToCheck = allCalls - ignored
        val callsToIgnore = callsToCheck.filter { callMayBeIgnored(it) }
        return ignored + callsToIgnore
    }

    private fun callMayBeIgnored(call: CallPredicate): Boolean {
        val approximation = approximationManager.underApproximations[call] ?: return false
        return approximation.approximations.isNotEmpty()
    }

    fun resolveCalls(model: RecoveredModel) {
        if (model.isFinal) return
        val calls = model.dependencies.groupBy { it.call }
        if (calls.isEmpty()) return
        if (calls.size > 1) return tryResolveMultipleCalls(model)
        val (call, dependencies) = calls.entries.last()
        resolveSingleCall(model.state, call, dependencies, model.pathVariables, model.tmpVariables)
    }

    private fun tryResolveMultipleCalls(model: RecoveredModel) {
//        val singleDepsPredicates = collectPredicatesWithSingleDependentTerm(model.state, model.dependencies)
        when {
//            singleDepsPredicates.isNotEmpty() -> singleDepsPredicates.forEach { (predicate, callIdx) ->
//                val depsToResolve = model.dependencies.filter { it.callIdx == callIdx }
//                val callToResolve = depsToResolve.first().call
//                resolveSingleCall(predicate.wrap(), callToResolve, depsToResolve, model.pathVariables, model.tmpVariables)
//            }
            else -> {
                val maxId = model.dependencies.map { it.callIdx }.maxOrNull() ?: error("impossible")
                val depsToResolve = model.dependencies.filter { it.callIdx == maxId }
                val callToResolve = depsToResolve.first().call
                resolveSingleCall(model.state, callToResolve, depsToResolve, model.pathVariables, model.tmpVariables)
            }
        }

    }

    private fun collectPredicatesWithSingleDependentTerm(state: PredicateState, dependencies: Set<TermDependency>): List<Pair<Predicate, Int>> {
        val memoryDependency = dependencies.filterIsInstance<TermDependency.MemoryDependency>().associateBy { it.memoryAccess }
        val callResultDependency = dependencies.filterIsInstance<TermDependency.CallResultDependency>().associateBy { it.term }
        val result = mutableListOf<Pair<Predicate, Int>>()
        PredicateCollector.collectIsInstance<Predicate>(state).forEach { predicate ->
            val dependentTerms = TermCollector.getFullTermSet(predicate).mapNotNull {
                when (it) {
                    is MemoryAccess<*> -> memoryDependency[it]?.callIdx
                    else -> callResultDependency[it]?.callIdx
                }
            }.distinct()
            when {
                predicate is MemoryAccess<*> && dependentTerms.isEmpty() -> {
                    val dependency = memoryDependency[predicate]
                    if (dependency != null) {
                        result += predicate to dependency.callIdx
                    }
                }
                predicate !is MemoryAccess<*> && dependentTerms.size == 1 -> {
                    val dependency = dependentTerms.first()
                    result += predicate to dependency
                }
            }
        }
        return result
    }

    private fun resolveSingleCall(
            state: PredicateStateWithPath,
            call: CallPredicate,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>, tmpVariables: Set<Term>
    ) {
        val inlineStatus = MethodManager.InlineManager.isInlinable((call.call as CallTerm).method)
        val callPreconditions = when (inlineStatus) {
            MethodManager.InlineManager.InlineStatus.INLINE -> resolveInlinableCall(state, call, dependencies, pathVariables, tmpVariables)
            MethodManager.InlineManager.InlineStatus.MAY_INLINE -> resolveOpenCall(state, call, dependencies, pathVariables, tmpVariables)
            MethodManager.InlineManager.InlineStatus.NO_INLINE -> resolveEmptyCall(state, call, dependencies, pathVariables, tmpVariables)
        }
        val renamedCallPreconditions = renameStateVariables(callPreconditions.state, callPreconditions.pathVariables, callPreconditions.tmpVariables, call, "pre")
        val renamedCallPostConditions = renameStateVariables(state, pathVariables, tmpVariables, call, "post")
        approximationManager.update(call, MethodUnderApproximation(renamedCallPreconditions, renamedCallPostConditions))
    }

    private fun renameStateVariables(
            state: PredicateStateWithPath,
            pathVariables: Set<Term>, tmpVariables: Set<Term>,
            call: CallPredicate,
            prefix: String
    ): PredicateStateWithPath {
        val rootVariableGenerator = variableGenerator.createNestedGenerator("${call.hashCode().absoluteValue}")
        val tmpVariableGenerator = rootVariableGenerator.createNestedGenerator(prefix).createNestedGenerator("tmp")
        val pathVariableGenerator = rootVariableGenerator.createNestedGenerator(prefix).createNestedGenerator("path")
        val tmpMapping = tmpVariables.associateWith { tmpVariableGenerator.generatorFor(it).createVar(it.type) }
        val pathMapping = pathVariables.associateWith { pathVariableGenerator.generatorFor(it).createVar(it.type) }
        val termMapper = TermRemapper(tmpMapping + pathMapping)
        return state.accept(termMapper::apply)
    }

    class OpenCallPreconditionMerge(
            val preconditions: Map<Method, RecoveredModel>,
            val scope: MemoryAccessScope,
            val version: MemoryVersion,
            method: Method
    ) : MethodImplementationMerge(method) {
        override val baseGenerator: VariableGenerator
            get() = VariableGenerator("resolved_impls")

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

        override fun createCast(builder: PredicateBuilder, lhs: Term, term: Term, type: KexType) =
                super.createCast(builder, lhs, term, type).withScopeInfo(scope).withMemoryVersion(version)

    }

    private fun resolveOpenCall(
            state: PredicateStateWithPath,
            call: CallPredicate,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>, tmpVariables: Set<Term>
    ): RecoveredModel {
        val callTerm = call.call as CallTerm
        val baseMethod = callTerm.method
        val implementations = MethodImplementations(methodAnalyzer.cm, methodAnalyzer.refinementsManager).collectImplementations(baseMethod)
        val preconditions = implementations.associateWith { method ->
            val newCall = CallTerm(callTerm.type, callTerm.owner, method, callTerm.instruction, callTerm.arguments, callTerm.memoryVersion)
            val newCallPredicate = CallPredicate(call.lhvUnsafe, newCall, call.type, call.location)
            val newDependencies = dependencies.map {
                when (it) {
                    is TermDependency.CallResultDependency -> TermDependency.CallResultDependency(it.term, it.callIdx, newCallPredicate)
                    is TermDependency.MemoryDependency -> TermDependency.MemoryDependency(it.memoryAccess, it.callIdx, newCallPredicate)
                }
            }
            resolveInlinableCall(state, newCallPredicate, newDependencies, pathVariables, tmpVariables)
        }
        val preconditionStates = preconditions.mapValues { (_, model) -> model.finalStateOrException() }.map { it.value to it.key }
        val preconditionMerger = OpenCallPreconditionMerge(preconditions, baseCallContext.scope, call.memoryVersion, baseMethod)
        val mergedState = preconditionMerger.mergeImplementations(preconditionStates)
        val mergedTmpVariables = preconditionMerger.tmpGenerator.generatedVariables().toSet()
        val mergedPathVariables = preconditionMerger.pathGenerator.generatedVariables().toSet()
        return RecoveredModel(mergedState, emptySet(), mergedPathVariables, mergedTmpVariables)
    }

    private fun resolveEmptyCall(
            state: PredicateStateWithPath,
            call: CallPredicate,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>, tmpVariables: Set<Term>
    ): RecoveredModel {
        TODO("No inline")
    }

    private fun resolveInlinableCall(
            state: PredicateStateWithPath,
            call: CallPredicate,
            dependencies: List<TermDependency>,
            pathVariables: Set<Term>, tmpVariables: Set<Term>
    ): RecoveredModel {
        check(currentCallContext == null) { "Incorrect scope state" }
        val (arguments, forwardMapping, backwardMapping) = collectArguments(state, call, dependencies, pathVariables, tmpVariables)
        val (stateWithDependencyInlined, memoryMapping, memoryVersionInfo) = inlineCallDependencies(state.state, call, dependencies)
        val stateToAnalyze = forwardMapping.apply(stateWithDependencyInlined)
        val positive = state.path
        val negative = state.negate().path
        val argument = CallResolveSolverQuery(stateToAnalyze, positive, negative, arguments, emptySet(), memoryVersionInfo, 0)
        val resultModel = analyzeState(argument)
        val resultState = backwardMapping.apply(resultModel.state.state)
        check(currentCallContext != null) { "Incorrect scope state" }
        val resultWithRestoredMemory = restoreStateMemory(resultState, memoryMapping)
        check(currentCallContext == null) { "Incorrect scope state" }
        val resultStateWithPath = PredicateStateWithPath(resultWithRestoredMemory, resultModel.state.path)
        return RecoveredModel(resultStateWithPath, emptySet(), resultModel.pathVariables, resultModel.tmpVariables)
    }

    private fun analyzeState(argument: CallResolveSolverQuery): RecoveredModel {
        check(currentCallContext != null) { "Incorrect scope state" }
        val resolver = CallResolver(methodAnalyzer, approximationManager, this)
        return resolver.callResolutionLoop(argument.wrap()).first()
    }


    private fun inlineCallDependencies(
            state: PredicateState,
            callPredicate: CallPredicate,
            dependencies: List<TermDependency>
    ): Triple<PredicateState, MemoryMappingType, MemoryVersionInfo> {
        val (methodState, finalVersions) = prepareInliningMethod(callPredicate, dependencies)
        val callMemoryVersion = callPredicate.memoryVersion
        currentCallContext = baseCallContext.nested(callMemoryVersion)
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
            mapping.getOrPut(it.withScope(baseCallContext.scope) to callMemoryVersion) {
                it.withScope(currentCallContext!!.scope) to MemoryVersion.initial()
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
        val result = MemoryMapper(backwardMapping).apply(state)
        currentCallContext = null
        return result
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
            val context = currentCallContext ?: error("Context must be not null here")
            if (descriptor.scopeInfo != context.scope) return null
            if (version != MemoryVersion.initial()) {
                error("Non mapped non initial")
            }
            val newDescriptor = descriptor.withScope(baseCallContext.scope)
            return newDescriptor to context.version
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
        val methodStateForInlining = ChainState(methodState, retvalBindings)

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

    private data class CallContext(val scope: MemoryAccessScope, val version: MemoryVersion) {
        fun nested(version: MemoryVersion) = CallContext(scope.withScope(version.machineName), version)

        companion object {
            val ROOT = CallContext(MemoryAccessScope.RootScope, MemoryVersion.default())
        }
    }

}


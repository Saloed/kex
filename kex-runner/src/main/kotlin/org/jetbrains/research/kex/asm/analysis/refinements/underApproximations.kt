package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.collection.dequeOf
import org.jetbrains.research.kex.state.CallApproximationState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.memory.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.transformer.RecollectingTransformer
import org.jetbrains.research.kex.state.transformer.Transformer
import org.jetbrains.research.kex.state.transformer.transform


class MethodApproximationManager {
    val underApproximations = hashMapOf<CallPredicate, MethodUnderApproximations>()
    fun update(call: CallPredicate, approximation: MethodUnderApproximation) {
        val currentApproximations = underApproximations.getOrDefault(call, MethodUnderApproximations())
        underApproximations[call] = currentApproximations.add(approximation)
    }

    fun extendWithUnderApproximations(state: PredicateState): PredicateState = ApproximationInliner(underApproximations).apply(state)
    fun correctMemoryAfterApproximation(state: PredicateState, memoryVersionInfo: MemoryVersionInfo): Pair<PredicateState, MemoryVersionInfo> {
        val corrector = ApproximationMemoryCorrector()
        val newState = corrector.apply(state)
        val newMemoryVersionInfo = MemoryUtils.memoryVersionInfo(newState)
        return newState to newMemoryVersionInfo
    }
}

data class MethodUnderApproximation(val pre: PredicateStateWithPath, val post: PredicateStateWithPath)
data class MethodUnderApproximations(val approximations: Set<MethodUnderApproximation> = emptySet()) {
    fun add(approximation: MethodUnderApproximation) = MethodUnderApproximations(approximations + approximation)
}


class ApproximationInliner(val approximations: Map<CallPredicate, MethodUnderApproximations>) : RecollectingTransformer<ApproximationInliner> {
    override val builders = dequeOf(StateBuilder())

    override fun transformCallPredicate(predicate: CallPredicate): Predicate {
        val transformedCall = super.transformCallPredicate(predicate) as CallPredicate
        val approximation = approximations[transformedCall]?.approximations
        val preconditions = approximation?.map { it.pre } ?: emptyList()
        val postconditions = approximation?.map { it.post } ?: emptyList()
        val defaultPostcondition = postconditions.map { it.negate() }.let { PredicateStateWithPath.chain(it) }
        currentBuilder += CallApproximationState(
                preconditions, postconditions,
                transformedCall, defaultPostcondition
        )
        return nothing()
    }
}

class ApproximationMemoryCorrector : MemoryVersionRecollectingTransformer() {
    private val callStateMapping = hashMapOf<CallApproximationState, PredicateState>()
    override fun transformCallApproximation(ps: CallApproximationState): PredicateState {
        val initialMemory = memoryState
        transform(ps.callState)
        val finalMemoryWithoutApproximation = memoryState
        val (finalMemoryWithApproximation, correctedState) = analyzeMemory(ps, initialMemory, ps.call.memoryVersion)
        finalMemoryWithoutApproximation.memory.forEach { (descriptor, version) ->
            val newVersion = finalMemoryWithApproximation.memory.getValue(descriptor)
            memoryState.mapping.getValue(descriptor)[version] = newVersion
        }
        callStateMapping[ps] = correctedState
        return ps
    }

    private fun analyzeMemory(state: CallApproximationState, initial: RecollectingMemoryState, newVersion: MemoryVersion): Pair<RecollectingMemoryState, PredicateState> {
        val mappedInitial = initial.memory.mapValues { (descriptor, version) ->
            initial.mapping.getValue(descriptor)[version]
                    ?: error("No version mapped")
        }
        val newMapping = initial.mapping.toMutableMap()
        mappedInitial.forEach { (descriptor, version) -> newMapping.getValue(descriptor)[version] = version }

        val mappingForPreconditions = newMapping.toMutableMap()
        mappingForPreconditions.forEach { (descriptor, versions) ->
            versions[newVersion] = mappedInitial[descriptor]
                    ?: error("Version not mapped")
        }
        val stateForPreconditions = RecollectingMemoryState(mappingForPreconditions, mappedInitial)
        val preconditionsMemoryTransformer = MemoryVersionRecollectingTransformer()
        preconditionsMemoryTransformer.apply(PredicateStateWithPath.choice(state.preconditions).state, stateForPreconditions)
        preconditionsMemoryTransformer.transformChoices(state.preconditions.map { it.path })
        val memoryAfterPreconditions = preconditionsMemoryTransformer.memoryState
        val transformedPreconditions = state.preconditions.map { it.accept { ps -> preconditionsMemoryTransformer.applyMapping(ps, memoryAfterPreconditions) } }

        val stateForPostConditions = RecollectingMemoryState(newMapping, memoryAfterPreconditions.memory)
        val postConditionsMemoryTransformer = MemoryVersionRecollectingTransformer()
        postConditionsMemoryTransformer.apply(state.callState, stateForPostConditions)
        postConditionsMemoryTransformer.transform(PredicateStateWithPath.choice(state.postconditions + state.defaultPostcondition).state)
        postConditionsMemoryTransformer.transformChoices((state.postconditions + state.defaultPostcondition).map { it.path })
        val memoryAfterPostConditions = postConditionsMemoryTransformer.memoryState
        val transformedCallState = postConditionsMemoryTransformer.applyMapping(state.callState, memoryAfterPostConditions)
        val transformedPostConditions = state.postconditions.map { it.accept { ps -> postConditionsMemoryTransformer.applyMapping(ps, memoryAfterPostConditions) } }
        val transformedDefaultPostCondition = state.defaultPostcondition.accept { ps -> postConditionsMemoryTransformer.applyMapping(ps, memoryAfterPostConditions) }

        val transformedState = CallApproximationState(transformedPreconditions, transformedPostConditions, transformedCallState, transformedDefaultPostCondition, state.call)
        return memoryAfterPostConditions to transformedState
    }

    override fun applyMapping(state: PredicateState, recollectedState: RecollectingMemoryState) = transform(state) {
        +ApproximationMemoryCorrectorStrictCallApproxMapper(callStateMapping)
        +ApproximationMemoryCorrectorMapper(recollectedState.mapping)
    }
}

class ApproximationMemoryCorrectorStrictCallApproxMapper(
        private val mapping: Map<CallApproximationState, PredicateState>
) : Transformer<ApproximationMemoryCorrectorStrictCallApproxMapper> {

    override fun transformCallApproximation(ps: CallApproximationState) = mapping[ps]
            ?: error("State is not mapped $ps")
}

class ApproximationMemoryCorrectorMapper(
        private val mapping: Map<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>
) : MemoryVersionTransformer {

    override fun transformCallApproximation(ps: CallApproximationState): PredicateState {
        // skip. Corrector assume that call approximations have correct memory versions
        return ps
    }

    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val descriptor = element.descriptor()
        val memoryMapping = mapping[descriptor] ?: error("No memory mapping for $descriptor")
        val newVersion = memoryMapping[element.memoryVersion]
                ?: error("No version mapping for $descriptor : ${element.memoryVersion}")
        return element.withMemoryVersion(newVersion)
    }
}

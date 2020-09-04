package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.CallApproximationState
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.Predicate

open class MemoryState(val memory: Map<MemoryDescriptor, MemoryVersion>) {
    open fun read(descriptor: MemoryDescriptor, memoryVersion: MemoryVersion) = this
    open fun write(descriptor: MemoryDescriptor, memoryVersion: MemoryVersion): MemoryState {
        val current = memory.getValue(descriptor)
        val newMemory = memory.plus(descriptor to current.increaseSubversion())
        return create(MemoryState(newMemory))
    }

    open fun reset(version: Int): MemoryState {
        val newMemory = memory.mapValues { it.value.resetToVersion(version) }
        return create(MemoryState(newMemory))
    }

    open fun merge(others: List<MemoryState>): MemoryState {
        val newMemory = memory.mapValues { (descriptor, defaultMemory) ->
            val alternatives = others.map { it.memory.getValue(descriptor) }
            MemoryVersion.merge(listOf(defaultMemory) + alternatives)
        }
        return create(MemoryState(newMemory))
    }

    open fun create(state: MemoryState) = state
}

open class MemorySimulator() : MemoryVersionTransformer {
    constructor(initialMemory: MemoryState) : this() {
        memory = initialMemory
    }

    lateinit var memory: MemoryState
    val memoryEvolution = arrayListOf<MemoryState>()

    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val descriptor = element.descriptor()
        when (element.accessType) {
            MemoryAccessType.WRITE -> updateState(memory.write(descriptor, element.memoryVersion))
            MemoryAccessType.READ -> updateState(memory.read(descriptor, element.memoryVersion))
        }
        return super.transformMemoryVersion(element)
    }

    override fun transformChoice(ps: ChoiceState): PredicateState {
        transformChoices(ps.choices)
        return ps
    }

    open fun transformChoices(choices: List<PredicateState>): List<PredicateState> {
        val memories = arrayListOf<MemoryState>()
        val initialState = memory
        for (branch in choices) {
            memory = initialState
            transform(branch)
            memories += memory
        }
        updateState(initialState.merge(memories))
        return choices
    }

    override fun transformCallApproximation(ps: CallApproximationState): PredicateState {
        transform(PredicateStateWithPath.choice(ps.preconditions).state)
        transformChoices(ps.preconditions.map { it.path })
        transform(ps.callState)
        transform(PredicateStateWithPath.choice(ps.postconditions + ps.defaultPostcondition).state)
        transformChoices((ps.postconditions + ps.defaultPostcondition).map { it.path })
        return ps
    }

    override fun transformCall(predicate: CallPredicate): Predicate {
        transform(predicate.call)
        updateState(memory.reset(predicate.memoryVersion.version))
        predicate.lhvUnsafe?.let { transform(it) }
        return predicate
    }

    private fun updateState(state: MemoryState) {
        memoryEvolution += state
        memory = state
    }

    override fun apply(ps: PredicateState): PredicateState {
        memoryEvolution += memory
        super.apply(ps)
        return ps
    }
}

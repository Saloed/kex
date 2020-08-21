package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term

internal class StrictMemoryVersionMapper(val mapping: Map<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>, val callDescriptor: MemoryDescriptor) : MemoryVersionTransformer {

    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val descriptor = element.descriptor()
        val memoryMapping = mapping[descriptor] ?: error("No memory mapping for $descriptor")
        val newVersion = memoryMapping[element.memoryVersion]
                ?: error("No version mapping for $descriptor : ${element.memoryVersion}")
        return element.withMemoryVersion(newVersion)
    }

    override fun transformCallTerm(term: CallTerm): Term {
        val callMapping = mapping[callDescriptor] ?: error("No memory mapping for $callDescriptor")
        val newVersion = callMapping[term.memoryVersion]
                ?: error("No version mapping for $callDescriptor : ${term.memoryVersion}")
        return term.withMemoryVersion(newVersion)
    }
}

internal class OptionalMemoryVersionMapper(val mapping: Map<MemoryDescriptor, Map<MemoryVersion, MemoryVersion>>, val callDescriptor: MemoryDescriptor? = null) : MemoryVersionTransformer {

    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        val descriptor = element.descriptor()
        val memoryMapping = mapping[descriptor] ?: return super.transformMemoryVersion(element)
        val newVersion = memoryMapping[element.memoryVersion] ?: return super.transformMemoryVersion(element)
        return element.withMemoryVersion(newVersion)
    }

    override fun transformCallTerm(term: CallTerm): Term {
        if (callDescriptor == null) return term
        val callMapping = mapping[callDescriptor] ?: return term
        val newVersion = callMapping[term.memoryVersion] ?: return term
        return term.withMemoryVersion(newVersion)
    }
}

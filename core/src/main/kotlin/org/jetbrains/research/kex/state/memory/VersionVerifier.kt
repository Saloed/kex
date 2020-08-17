package org.jetbrains.research.kex.state.memory

import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term

internal object VersionVerifier : MemoryVersionTransformer {
    override fun <T> transformMemoryVersion(element: MemoryAccess<T>): T {
        checkMemoryVersion(element.memoryVersion, element)
        return super.transformMemoryVersion(element)
    }

    override fun transformCallTerm(term: CallTerm): Term {
        checkMemoryVersion(term.memoryVersion, term)
        return super.transformCallTerm(term)
    }

    private fun checkMemoryVersion(version: MemoryVersion, element: Any) {
        check(version.type != MemoryVersionType.DEFAULT) { "Default memory: $element" }
        check(version.version in 0..999) { "Memory version may be incorrect: $version | $element" }
    }
}
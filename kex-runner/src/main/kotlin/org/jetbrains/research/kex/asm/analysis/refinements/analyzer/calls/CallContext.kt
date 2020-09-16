package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import org.jetbrains.research.kex.state.memory.MemoryAccessScope
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.util.VariableGenerator

data class CallContext private constructor(
        val scope: MemoryAccessScope,
        val variableGenerator: VariableGenerator,
        private val versionUnsafe: MemoryVersion?,
        private val parentUnsafe: CallContext?
) {
    val parent: CallContext
        get() = parentUnsafe ?: error("Root context has no parent")

    val version: MemoryVersion
        get() = versionUnsafe ?: error("Root context has no version")

    fun nested(version: MemoryVersion) = CallContext(
            scope.withScope(version.machineName),
            variableGenerator.createNestedGenerator("x"),
            version,
            this
    )

    companion object {
        val ROOT = CallContext(
                MemoryAccessScope.RootScope,
                VariableGenerator("cr"),
                null, null
        )
    }
}

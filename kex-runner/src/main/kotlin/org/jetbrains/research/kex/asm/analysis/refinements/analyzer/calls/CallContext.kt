package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.calls

import org.jetbrains.research.kex.state.memory.MemoryAccessScope
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.util.VariableGenerator

data class CallContext(
        val scope: MemoryAccessScope,
        val version: MemoryVersion,
        val variableGenerator: VariableGenerator,
        private val parentUnsafe: CallContext?
) {
    val parent: CallContext
            get() = parentUnsafe ?: error("Root context has no parent")

    fun nested(version: MemoryVersion) = CallContext(
            scope.withScope(version.machineName),
            version,
            variableGenerator.createNestedGenerator("x"),
            this
    )

    companion object {
        val ROOT = CallContext(
                MemoryAccessScope.RootScope,
                MemoryVersion.default(),
                VariableGenerator("cr"),
                null
        )
    }
}

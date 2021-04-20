package org.jetbrains.research.kex.smt.z3.fixpoint.declarations

import org.jetbrains.research.kex.state.memory.MemoryVersionInfo

data class ArgumentDeclarations private constructor(val declarations: List<Declaration>) {
    operator fun get(idx: Int) = declarations.getOrNull(idx)
        ?: error("Model expression has non argument term")

    fun initializeMemoryVersions(memoryVersionInfo: MemoryVersionInfo): ArgumentDeclarations {
        val mutableDeclarations = declarations.toMutableList()
        mutableDeclarations.replaceAll {
            if (it !is Declaration.Memory) return@replaceAll it
            val originalVersion = memoryVersionInfo.findMemoryVersion(it.descriptor, it.version)
                    ?: error("No such memory info $it")
            Declaration.Memory(it.descriptor, originalVersion, it.info)
        }
        return ArgumentDeclarations(mutableDeclarations)
    }

    companion object {
        fun create(declarations: List<Declaration>) = ArgumentDeclarations(declarations.sortedBy { "$it" })
        fun createFromOrdered(declarations: List<Declaration>) = ArgumentDeclarations(declarations)
    }
}

package org.jetbrains.research.kex.state.term

import org.jetbrains.research.kex.state.MemoryVersion

interface MemoryDependentTerm {
    val memoryVersion: MemoryVersion
    fun withMemoryVersion(memoryVersion: MemoryVersion): Term
}

package org.jetbrains.research.kex.smt.z3.fixpoint.converter

import com.microsoft.z3.Expr
import org.jetbrains.research.kex.smt.z3.*
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.memory.MemoryVersion

class Z3ContextWithMemoryArrays(factory: ExprFactory_) : Z3Context(factory, BASE_LOCAL_PTR, BASE_STATIC_PTR) {

    fun setUpInitialMemory(ctx: SolverContext_, memories: Map<MemoryDescriptor, Expr>) {
        val arrays = memories.mapValues { (_, expr) -> Array_<Dynamic_, Ptr_>(ctx, expr) }
        val z3Memories = arrays.mapValues { (_, array) -> Memory_<Ptr_, Dynamic_>(ctx, Dynamic_::class, array) }
        val versionedMemories = z3Memories.mapValues { (_, memory) -> VersionedMemory(memory, MemoryVersion.initial(), Dynamic_::class) }
        versionedMemories.forEach { (descriptor, memory) ->
            initialMemories[descriptor] = memory
        }
    }

}
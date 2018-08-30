package org.jetbrains.research.kex.asm.state

import org.jetbrains.research.kex.asm.transform.LoopDeroller
import org.jetbrains.research.kex.asm.transform.MethodInliner
import org.jetbrains.research.kex.util.error
import org.jetbrains.research.kex.util.log
import org.jetbrains.research.kfg.analysis.IRVerifier
import org.jetbrains.research.kfg.analysis.LoopAnalysis
import org.jetbrains.research.kfg.analysis.LoopSimplifier
import org.jetbrains.research.kfg.ir.Method

object PredicateStateAnalysis {
//    val builders = hashMapOf<Method, PredicateStateBuilder>()

    private fun prepareMethod(method: Method) {
        MethodInliner(method).visit()

        val la = LoopAnalysis(method)
        la.visit()

        if (la.loops.isNotEmpty()) {
            val simplifier = LoopSimplifier(method)
            simplifier.visit()
            val deroller = LoopDeroller(method)
            deroller.visit()
        }
        IRVerifier(method).visit()
    }

    private fun createMethodBuilder(method: Method): PredicateStateBuilder {
        prepareMethod(method)

        val psb = PredicateStateBuilder(method)
        try {
            psb.visit()
        } catch (e: NoTopologicalSortingError) {
            log.error(e)
        }
        return psb
    }

    // no cashing for now
    fun builder(method: Method) = createMethodBuilder(method)
//    fun builder(method: Method) = builders.getOrPut(method) {
//        log.error("Creating new builder for $method")
//        createMethodBuilder(method)
//    }
}
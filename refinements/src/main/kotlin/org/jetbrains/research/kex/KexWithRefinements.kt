package org.jetbrains.research.kex

import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.transform.LoopDeroller
import org.jetbrains.research.kfg.analysis.LoopSimplifier
import java.net.URLClassLoader

class KexWithRefinements(args: Array<String>) : Kex(args) {
    override fun refinements(analysisContext: ExecutionContext) {
        val debugMethods = cmd.getCmdValue("debugMethods")
                ?.let { it.split(",").map { it.trim() } } ?: emptyList()
        val psa = PredicateStateAnalysis(analysisContext.cm)
        updateClassPath(analysisContext.loader as URLClassLoader)
        runPipeline(analysisContext) {
            +LoopSimplifier(analysisContext.cm)
            +LoopDeroller(analysisContext.cm)
            +psa
            +MethodRefinements(analysisContext, psa, debugMethods)
        }
    }
}

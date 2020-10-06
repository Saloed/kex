package org.jetbrains.research.kex.refinements.analyzer.method

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.refinements.Refinements
import org.jetbrains.research.kex.refinements.analyzer.MethodExecutionPathsAnalyzer
import org.jetbrains.research.kex.refinements.analyzer.calls.CallInliner
import org.jetbrains.research.kex.refinements.analyzer.exceptions.ExceptionSource
import org.jetbrains.research.kex.refinements.analyzer.exceptions.ExceptionSourceBuilder
import org.jetbrains.research.kex.refinements.analyzer.sources.CallResolvingRefinementSourcesAnalyzer
import org.jetbrains.research.kex.state.memory.MemoryVersioner
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method

class SimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    override fun analyze(): Refinements {
        val methodPaths = MethodExecutionPathsAnalyzer(cm, psa, method)
        val inliner = CallInliner(cm, psa, this)
        val statePrepared = inliner.apply(methodPaths.methodRawFullState()).optimize()
        val versioner = MemoryVersioner()
        val state = versioner.apply(statePrepared)
        val memoryVersionInfo = versioner.memoryInfo()

        val throwSources = methodPaths.throws.map { ExceptionSource.MethodException(it) }
        val callSources = inliner.callPathConditions.map { (call, pc) -> ExceptionSource.CallException(call, pc) }
        val sourceBuilder = ExceptionSourceBuilder(method, throwSources + callSources)
        val allSources = sourceBuilder.buildExceptionSources()
        val allNormal = sourceBuilder.buildNormals(methodPaths.returns)

        log.info("Analyze: $method")
        log.debug("State:\n$state\nExceptions:\n$allSources\nNormal:\n$allNormal")

        return CallResolvingRefinementSourcesAnalyzer(this).analyze(state, allNormal, allSources, memoryVersionInfo)
//        return CallResolvingRefinementSourcesSingleAnalyzer(this).analyze(state, allNormal, allSources, memoryVersionInfo)
    }
}

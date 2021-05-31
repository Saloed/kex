package org.jetbrains.research.kex.refinements.analyzer.method

import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.refinements.Refinements
import org.jetbrains.research.kex.refinements.analyzer.exceptions.ExceptionSource
import org.jetbrains.research.kex.refinements.analyzer.exceptions.RefinementSourceBuilder
import org.jetbrains.research.kex.refinements.analyzer.sources.CallResolvingRefinementSourcesAnalyzer
import org.jetbrains.research.kex.refinements.analyzer.utils.MethodExecutionPathsAnalyzer
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method

class SimpleMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {

    override fun analyze(): Refinements {
        val methodPaths = MethodExecutionPathsAnalyzer(cm, psa, method)
        val (statePrepared, callPathConditions) = inlineCalls(methodPaths.methodRawFullState())
        val (state, memoryVersionInfo) = buildMemoryVersions(statePrepared)

        val throwSources = methodPaths.throws.map { ExceptionSource.MethodException(it) }
        val callSources = callPathConditions.map { (call, pc) -> ExceptionSource.CallException(call, pc) }
        val sourceBuilder = RefinementSourceBuilder(method, throwSources + callSources)
        val allSources = sourceBuilder.buildExceptionSources()
        val allNormal = sourceBuilder.buildNormals(methodPaths.returns)

        log.info("Analyze: $method")
        log.debug("State:\n$state\nExceptions:\n$allSources\nNormal:\n$allNormal")

        return CallResolvingRefinementSourcesAnalyzer(this).analyze(state, allNormal, allSources, memoryVersionInfo)
    }
}

package org.jetbrains.research.kex.asm.analysis.refinements.analyzer.method

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.analysis.refinements.Refinement
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.MethodImplementationMerge
import org.jetbrains.research.kex.asm.analysis.refinements.analyzer.MethodImplementations
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.state.transformer.MethodFunctionalInliner
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method

class OpenMethodAnalyzer(cm: ClassManager, psa: PredicateStateAnalysis, mr: MethodRefinements, method: Method) : MethodAnalyzer(cm, psa, mr, method) {
    override fun analyze(): Refinements {
        val implementations = MethodImplementations(cm, refinementsManager).collectImplementations(method)
        val refinements = implementations.map {
            when (it) {
                method -> NoInliningSimpleMethodAnalyzer(cm, psa, refinementsManager, it).analyze()
                else -> findRefinement(it)
            }
        }
        return when (refinements.size) {
            0 -> {
                log.warn("No implementations found for method $method")
                Refinements.unknown(method)
            }
            1 -> refinements.first().let { Refinements.create(method, it.value) }
            else -> mergeRefinements(refinements)
        }
    }

    private fun mergeRefinements(refinements: List<Refinements>) = refinements
            .flatMap { ref -> ref.value.map { it to ref.method } }
            .groupBy { it.first.criteria }
            .mapValues { it.value.map { (ref, method) -> ref.state to method } }
            .mapValues { MethodImplementationMerge(method).mergeImplementations(it.value) }
            .mapValues { Refinement.create(it.key, it.value) }
            .let { Refinements.create(method, it.values.toList()) }

    override fun MethodFunctionalInliner.TransformationState.getMethodStateAndRefinement() = error("Unavailable")
}
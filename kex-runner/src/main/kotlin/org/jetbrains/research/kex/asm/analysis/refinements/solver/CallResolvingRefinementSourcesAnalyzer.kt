package org.jetbrains.research.kex.asm.analysis.refinements.solver

import com.abdullin.kthelper.logging.debug
import com.abdullin.kthelper.logging.log
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.asm.analysis.refinements.*
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.transformer.PredicateCollector

class CallResolvingRefinementSourcesAnalyzer(methodAnalyzer: MethodAnalyzer) : RefinementSourcesAnalyzer(methodAnalyzer) {
    override fun createRefinements(refinements: List<Refinement>): Refinements = when {
        refinements.any { !refinementIsCorrect(it) } -> throw IllegalStateException("Incorrect refinement")
        else -> super.createRefinements(refinements)
    }

    @Serializable
    data class SolverQueryArgument(val state: PredicateState, val normals: PredicateState, val sources: List<PredicateState>) : CallResolver.Argument<SolverQueryArgument> {
        override fun transform(transformer: (PredicateState) -> PredicateState): SolverQueryArgument =
                SolverQueryArgument(transformer(state), transformer(normals), sources.map(transformer))
    }

    override fun queryRefinementSources(state: PredicateState, normals: PredicateState, sources: RefinementSources): Refinements {
        if (sources.value.isEmpty()) return Refinements.unknown(methodAnalyzer.method)
        val conditions = sources.value.map { it.condition }
        val argument = SolverQueryArgument(state, normals, conditions)
        val callResolver = CallResolver(methodAnalyzer, methodsUnderApproximations)
        val result = callResolver.callResolutionLoopMany(argument) { arg ->
            log.debug(arg)
            val result = FixpointSolver(methodAnalyzer.cm).query(
                    {
                        it.dumpSolverArguments(arg)
                        mkFixpointQueryV2(arg.state, arg.sources, arg.normals)
                    },
                    { ex ->
                        dumpSolverArguments(arg)
                        throw IllegalStateException("$ex")
                    }
            )
            log.debug(result)
            result
        }
        val refinements = sources.value.zip(result).map { (src, answer) -> Refinement.create(src.criteria, answer) }
        return Refinements.create(methodAnalyzer.method, refinements)
    }

    private fun refinementIsCorrect(refinement: Refinement): Boolean {
        if (PredicateCollector.collectIsInstance<CallPredicate>(refinement.state).isNotEmpty()) return false
        // todo: maybe more checks
        return true
    }


    companion object {
        private val methodsUnderApproximations = MethodApproximationManager()
    }
}
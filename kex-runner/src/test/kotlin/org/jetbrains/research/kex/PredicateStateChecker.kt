package org.jetbrains.research.kex

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.smt.Result
import org.jetbrains.research.kex.smt.z3.Z3Solver
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.ValueTerm
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kex.state.transformer.TermRemapper
import org.jetbrains.research.kex.state.transformer.collectVariables
import org.jetbrains.research.kfg.type.TypeFactory

class PredicateStateChecker(private val tf: TypeFactory) {
    fun check(expected: PredicateStateWithPath, actual: PredicateStateWithPath): Boolean {
        if (expected == actual) return true

        val expectedVariables = expected.variables()
        val actualVariables = actual.variables()
        val sameVariables = expectedVariables intersect actualVariables
        val expectedWithCorrectedVariables = expected.remapVariables(expectedVariables - sameVariables, "expected")
        val actualWithCorrectedVariables = actual.remapVariables(actualVariables - sameVariables, "actual")

        log.debug("Actual: $actualWithCorrectedVariables")
        log.debug("Expected: $expectedWithCorrectedVariables")

        val solver = Z3Solver(tf)
        val solution = solver.isAlwaysEqual(actualWithCorrectedVariables, expectedWithCorrectedVariables)
        return when (solution) {
            is Result.UnsatResult -> true
            is Result.SatResult -> {
                log.debug("Check failed: $solution")
                log.debug("${solution.model}")
                false
            }
            is Result.UnknownResult -> {
                log.debug("Check failed: $solution")
                log.debug(solution.reason)
                false
            }
        }
    }

    private fun PredicateStateWithPath.variables() = (collectVariables(state) + collectVariables(path)).filterIsInstance<ValueTerm>().toSet()
    private fun PredicateStateWithPath.remapVariables(variables: Set<Term>, prefix: String): PredicateStateWithPath {
        val mapping = variables.associateWith { term { value(it.type, "${prefix}_${it.name}") } }
        val mapper = TermRemapper(mapping)
        return accept(mapper::apply)
    }

}
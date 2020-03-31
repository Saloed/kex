package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.KexRunnerTest
import org.jetbrains.research.kex.asm.analysis.MethodRefinements
import org.jetbrains.research.kex.asm.analysis.refinements.Refinement
import org.jetbrains.research.kex.asm.analysis.refinements.RefinementCriteria
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.transform.LoopDeroller
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.predicate.PredicateBuilder
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.analysis.LoopSimplifier
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.visitor.executePipeline
import org.junit.jupiter.api.TestInstance
import java.net.URLClassLoader
import kotlin.test.assertEquals

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class RefinementTest(val suiteName: String) : KexRunnerTest() {

    val refinementsPackageName = "$packageName/refinements"
    val refinementsPackage = Package("$refinementsPackageName/*")
    val `class`: Class
        get() = cm["$refinementsPackageName/$suiteName"]

    private val psa = PredicateStateAnalysis(analysisContext.cm)

    init {
        updateClassPath(analysisContext.loader as URLClassLoader)
        executePipeline(analysisContext.cm, refinementsPackage) {
            +LoopSimplifier(analysisContext.cm)
            +LoopDeroller(analysisContext.cm)
            +psa
        }
        clearClassPath()
    }

    fun run(method: String, expected: RefinementBuilder.() -> Unit) {
        val testMethod = findMethod(method)
        val refinements = refinementsForMethod(testMethod)
        val expectedRefinements = RefinementBuilder(testMethod).apply { expected() }.refinements()
        assertRefinementsEqual(expectedRefinements, refinements)
    }

    fun nestedClass(name: String) = "$refinementsPackageName/$suiteName\$$name"

    private fun assertRefinementsEqual(expected: Refinements, actual: Refinements) {
        if (expected == actual) return
        val expectedRefinements = expected.value.map { it.criteria to it }.toMap()
        val actualRefinements = actual.value.map { it.criteria to it }.toMap()
        assertEquals(expectedRefinements.keys, actualRefinements.keys, "Refinement criterias not equal")
        val refinements = expectedRefinements.map { (criteria, reft) -> reft to actualRefinements[criteria]!! }
        for ((expectedReft, actualReft) in refinements) {
            assertPredicateStateEquals(expectedReft.state, actualReft.state)
        }
    }

    private fun assertPredicateStateEquals(expected: PredicateState, actual: PredicateState) {
        if (expected == actual) return
        val solver = Z3FixpointSolver(cm.type)
        val equality = solver.checkEquality(expected, actual)
        if (!equality) {
            assertEquals(expected, actual, "Refinement states not equal")
        }
    }

    private fun findMethod(name: String) = `class`.methods.find { it.name == name }
            ?: throw IllegalStateException("Method $name not found in $`class`")

    private fun refinementsForMethod(method: Method): Refinements {
        val refinements = MethodRefinements(analysisContext, psa)
        refinements.visit(method)
        return refinements.getOrComputeRefinement(method)
    }

    inner class RefinementBuilder(val method: Method) {
        val values = arrayListOf<Refinement>()

        fun refinement(exception: Exception, psBuilder: StateBuilder.() -> PredicateState) {
            val criteria = criteriaForException(exception)
            val ps = StateBuilder().psBuilder()
            values.add(Refinement.create(criteria, ps))
        }

        fun refinements() = Refinements(values, method)

        private fun criteriaForException(exception: Exception): RefinementCriteria {
            val cls = cm[exception::class.java.name.replace('.', '/')]
            val kfgType = ClassType(cls)
            return RefinementCriteria(kfgType)
        }

    }

}
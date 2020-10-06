package org.jetbrains.research.kex.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.KexTest
import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kex.PredicateStateChecker
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.transform.LoopDeroller
import org.jetbrains.research.kex.random.easyrandom.EasyRandomDriver
import org.jetbrains.research.kex.serialization.RefinementsKexSerializer
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.StateBuilder
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.memory.MemoryVersioner
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.analysis.LoopSimplifier
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.type.ClassType
import org.jetbrains.research.kfg.type.NullType
import org.jetbrains.research.kfg.visitor.executePipeline
import org.junit.jupiter.api.TestInstance
import java.net.URLClassLoader
import kotlin.test.assertEquals

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class RefinementTest(
        val suiteName: String,
        includeStdlib: Boolean = false,
        failOnError: Boolean = true
) : KexTest(includeStdlib, failOnError) {
    val refinementsPackageName = "$packageName/refinements"
    val refinementsPackage = Package("$refinementsPackageName/*")
    val `class`: Class
        get() = cm["$refinementsPackageName/$suiteName"]

    private val psa: PredicateStateAnalysis
    private val analysisContext: ExecutionContext

    init {
        analysisContext = ExecutionContext(cm, URLClassLoader(emptyArray()), EasyRandomDriver())
        psa = PredicateStateAnalysis(analysisContext.cm)
        executePipeline(analysisContext.cm, refinementsPackage) {
            +LoopSimplifier(analysisContext.cm)
            +LoopDeroller(analysisContext.cm)
            +psa
        }
    }

    fun run(method: String, expected: RefinementBuilder.() -> Unit) {
        log.info("Run test: $method")
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

    fun PredicateState.withMemoryVersions() = MemoryVersioner().apply(this)

    private fun assertPredicateStateEquals(expected: PredicateStateWithPath, actual: PredicateStateWithPath) {
        val equality = PredicateStateChecker(cm.type).check(expected, actual)
        if (!equality) {
            assertEquals(expected, actual, "Refinement states not equal")
        }
    }


    private fun findMethod(name: String) = `class`.methods.find { it.name == name }
            ?: throw IllegalStateException("Method $name not found in $`class`")

    fun refinementsForMethod(method: Method): Refinements {
        val refinements = MethodRefinements(analysisContext, psa)
        return refinements.getOrComputeRefinement(method)
    }

    enum class SpecialExceptions {
        NULL, NOTHING
    }

    inner class RefinementBuilder(val method: Method) {
        val values = arrayListOf<Refinement>()

        fun refinement(exception: SpecialExceptions, psBuilder: StateBuilder.() -> PredicateState) {
            val criteria = criteriaForException(exception)
            refinement(criteria, psBuilder)
        }

        fun refinement(exception: Exception, psBuilder: StateBuilder.() -> PredicateState) {
            val criteria = criteriaForException(exception)
            refinement(criteria, psBuilder)
        }

        fun refinement(criteria: RefinementCriteria, psBuilder: StateBuilder.() -> PredicateState) {
            val ps = StateBuilder().psBuilder()
            values.add(Refinement.create(criteria, PredicateStateWithPath(emptyState(), ps)))
        }

        fun refinementFromResource(exception: Exception) {
            val criteria = criteriaForException(exception)
            val resourceName = "${suiteName}__${method.name}.json"
            val resource = RefinementTest::class.java.getResource(resourceName)
            val resourceContent = resource.readText()
            val ps = RefinementsKexSerializer(cm).fromJson<PredicateState>(resourceContent)
            values.add(Refinement.create(criteria, PredicateStateWithPath(emptyState(), ps)))
        }

        fun refinements() = Refinements.create(method, values)

        private fun criteriaForException(exception: Exception?): RefinementCriteria {
            if (exception == null) return RefinementCriteria(NullType)
            val cls = cm[exception::class.java.name.replace('.', '/')]
            val kfgType = ClassType(cls)
            return RefinementCriteria(kfgType)
        }

        private fun criteriaForException(exception: SpecialExceptions) = when (exception) {
            SpecialExceptions.NULL -> RefinementCriteria(NullType)
            SpecialExceptions.NOTHING -> RefinementCriteria(ClassType(cm["kotlin/KotlinNothingValueException"]))
        }

    }

}
package org.jetbrains.research.kex.asm.analysis

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst
import org.jetbrains.research.kfg.visitor.MethodVisitor

class MethodRefinements(
        private val ctx: ExecutionContext,
        private val psa: PredicateStateAnalysis
) : MethodVisitor {

    override val cm: ClassManager get() = ctx.cm

    override fun cleanup() {}


    private val methodsToAnalyze = listOf("dummy", "dummy2", "dummy3", "fooWithoutStdlib", "foo", "test")
//    private val methodsToAnalyze = listOf("dummy3")

    override fun visit(method: Method) {
        super.visit(method)

        if (method.name !in methodsToAnalyze) {
            return
        }
        analyzeMethodPaths(method)
    }


    private fun methodFullState(method: Method): PredicateState {
        val builder = psa.builder(method)
        var state: PredicateState = builder.getMethodFullState()
        state = MethodInliner(method, psa).apply(state)
        state = IntrinsicAdapter.apply(state)
        state = Optimizer().apply(state)
        state = ConstantPropagator.apply(state)
        state = BoolTypeAdapter(method.cm.type).apply(state)
        state = ArrayBoundsAdapter().apply(state)

        state = MemorySpacer(state).apply(state)
        state = Optimizer().apply(state)
        return state
    }


    private fun findExceptionRelatedPaths(method: Method): Pair<List<PredicateState>, List<PredicateState>> {
        val builder = psa.builder(method)
        val instructions = builder.methodExitInstructions()
        val throws = instructions.filterIsInstance<ThrowInst>()
                .mapNotNull { builder.getInstructionState(it) }
                .map { it.filterByType(PredicateType.Path()) }
                .map { it.simplify() }
        val normal = instructions.filterNot { it is ThrowInst }
                .mapNotNull { builder.getInstructionState(it) }
                .map { it.filterByType(PredicateType.Path()) }
                .map { it.simplify() }
        return normal to throws
    }


    private fun analyzeMethodPaths(method: Method) {
        val state = methodFullState(method)
        val (normalPaths, exceptionPaths) = findExceptionRelatedPaths(method)

        log.info("Start fixpoint: ${method.name}")

        val allExceptions = ChoiceState(exceptionPaths)
        val allNormal = ChoiceState(normalPaths)

        log.info("State:\n$state\nPositive:\n$allExceptions\nNegative:\n$allNormal")

        val slv = Z3FixpointSolver(method.cm.type)
        val result = slv.mkFixpointQuery(state, allExceptions, allNormal)

        log.info("Result:\n$result")

    }

}

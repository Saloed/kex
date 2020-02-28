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

    private val debugMethods: List<String> = listOf()

    override val cm: ClassManager get() = ctx.cm

    override fun cleanup() {}


    override fun visit(method: Method) {
        super.visit(method)
        if (debugMethods.isNotEmpty() && method.name !in debugMethods) return
        try {
            analyzeMethodPaths(method)
        } catch (ex: Exception) {
            log.error("Error in analysis: method $method", ex)
        }
    }


    private fun methodFullState(method: Method): PredicateState =
            transform(psa.builder(method).getMethodFullState()) {
                +MethodInliner(method, psa)
                +IntrinsicAdapter
                +Optimizer()
                +ConstantPropagator
                +BoolTypeAdapter(cm.type)
                +ArrayBoundsAdapter()
                +Optimizer()
            }.let { state -> MemorySpacer(state).apply(state) }


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

        log.info("Start analysis: ${method.name}")

        val allExceptions = ChoiceState(exceptionPaths)
        val allNormal = ChoiceState(normalPaths)

        if (allExceptions.isEmpty || allNormal.isEmpty) {
            log.info("No paths to analyse")
            return
        }

        log.info("State:\n$state\nPositive:\n$allExceptions\nNegative:\n$allNormal")

        val slv = Z3FixpointSolver(cm.type)
        val result = slv.mkFixpointQuery(state, allExceptions, allNormal)

        log.info("Result:\n$result")

    }

}

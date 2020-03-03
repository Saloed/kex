package org.jetbrains.research.kex.asm.analysis

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.state.PredicateStateBuilder
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst
import org.jetbrains.research.kfg.visitor.MethodVisitor

interface MethodRefinementsManager {
    fun gerOrComputeRefinement(method: Method): PredicateState
}

class MethodRefinements(
        private val ctx: ExecutionContext,
        private val psa: PredicateStateAnalysis,
        private val debugMethods: List<String> = emptyList()
) : MethodVisitor, MethodRefinementsManager {

    private val knownRefinements: HashMap<Method, PredicateState> = hashMapOf()

    override val cm: ClassManager get() = ctx.cm

    override fun cleanup() {}

    override fun visit(method: Method) {
        super.visit(method)
        if (debugMethods.isNotEmpty() && method.name !in debugMethods) return
        gerOrComputeRefinement(method)
    }

    override fun gerOrComputeRefinement(method: Method): PredicateState {
        val refinement = knownRefinements[method] ?: analyzeMethod(method)
        knownRefinements[method] = refinement
        return refinement
    }

    private fun analyzeMethod(method: Method) = try {
        analyzeMethodPaths(method)
    } catch (ex: Exception) {
        log.error("Error in analysis: method $method", ex)
        falseState()
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
        val normal = instructions.filterNot { it is ThrowInst }
                .mapNotNull { builder.getInstructionState(it) }
                .map { it.filterByType(PredicateType.Path()) }
        return normal to throws
    }

    private fun nestedMethodsRefinements(method: Method): PredicateState {
        val builder = psa.builder(method)
        return MethodCallCollector.calls(cm, method)
                .map { processMethodCall(it, builder) }
                .let { ChoiceState(it) }
    }

    private fun processMethodCall(call: CallInst, psb: PredicateStateBuilder): PredicateState {
        val state = (psb.getInstructionState(call) ?: BasicState())
                .filter { it is CallPredicate || it.type == PredicateType.Path() }
        return transform(state) {
            +MethodRefinementsInliner(this@MethodRefinements)
        }
    }

    private fun PredicateState.optimize() = transform(this) {
        +ConstantPropagator
        +Optimizer()
    }

    private fun analyzeMethodPaths(method: Method): PredicateState {
        log.info("Start analysis: $method")

        val state = methodFullState(method)
        val (normalPaths, exceptionPaths) = findExceptionRelatedPaths(method)
        val nestedCallExceptions = nestedMethodsRefinements(method)

        val methodExceptions = ChoiceState(exceptionPaths)
        val methodNormal = ChoiceState(normalPaths)

        val allExceptions = ChoiceState(listOf(methodExceptions, nestedCallExceptions)).optimize()
        val allNormal = ChainState(methodNormal, nestedCallExceptions.not()).optimize()

        log.info("Analyze: $method")
        log.info("State:\n$state\nExceptions:\n$allExceptions\nNormal:\n$allNormal")

        val result = analyzeMethodPaths(state, allNormal, allExceptions)

        log.info("Result $method:\n$result")
        return result
    }

    private fun analyzeMethodPaths(state: PredicateState, normalPaths: PredicateState, exceptionPaths: PredicateState): PredicateState = when {
        normalPaths.evaluatesToTrue() && exceptionPaths.evaluatesToFalse() -> falseState()
        normalPaths.evaluatesToFalse() && exceptionPaths.evaluatesToTrue() -> trueState()
        normalPaths.evaluatesToTrue() && exceptionPaths.evaluatesToTrue() -> {
            log.error("Normal and Exception paths are always true")
            falseState()
        }
        normalPaths.evaluatesToFalse() && exceptionPaths.evaluatesToFalse() -> {
            log.error("Normal and Exception paths are always false")
            falseState()
        }
        else -> try {
            val result = Z3FixpointSolver(cm.type).mkFixpointQuery(state, exceptionPaths, normalPaths)
            when (result) {
                is Z3FixpointSolver.FixpointResult.Sat -> result.result
                else -> falseState()
            }
        } catch (ex: Z3FixpointSolver.FixpointQueryException) {
            log.error("Bad fixpoint query: ${ex.status}")
            analyzeFixpointQueryExcpetionStatus(ex.status)
        }
    }

    private fun analyzeFixpointQueryExcpetionStatus(status: Z3FixpointSolver.QueryCheckStatus): PredicateState = when {
        status.stateNotPossible -> falseState()
        status.exclusivenessNotPossible -> falseState()
        !status.positiveNotPossible && status.negativeNotPossible -> falseState()
        status.positiveNotPossible && !status.negativeNotPossible -> trueState()
        else -> falseState()
    }


    class MethodCallCollector(override val cm: ClassManager) : MethodVisitor {
        override fun cleanup() {}

        val calls = mutableSetOf<CallInst>()

        override fun visitCallInst(inst: CallInst) {
            super.visitCallInst(inst)
            calls.add(inst)
        }

        companion object {
            fun calls(cm: ClassManager, method: Method): List<CallInst> {
                val collector = MethodCallCollector(cm)
                collector.visit(method)
                return collector.calls.toList()
            }
        }
    }

}


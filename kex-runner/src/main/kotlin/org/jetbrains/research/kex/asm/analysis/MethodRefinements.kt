package org.jetbrains.research.kex.asm.analysis

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.ir.value.instruction.CastInst
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst
import org.jetbrains.research.kfg.type.Type
import org.jetbrains.research.kfg.visitor.MethodVisitor
import ru.spbstu.ktuples.zip


class MethodRefinements(
        private val ctx: ExecutionContext,
        private val psa: PredicateStateAnalysis,
        private val debugMethods: List<String> = emptyList()
) : MethodVisitor {

    data class RefinementCriteria(val type: Type)

    data class Refinement(val value: Map<RefinementCriteria, PredicateState>) {

        fun forTarget(type: RefinementCriteria): PredicateState {
            val positive = value[type] ?: return falseState()
            val negative = value.filterKeys { it != type }.values.toList()
            return ChainState(
                    positive,
                    ChoiceState(negative).not()
            )
        }

        fun allTargets() = value.keys.map { it to forTarget(it) }

        fun allPaths(): PredicateState = ChoiceState(value.values.toList())

        companion object {
            fun unknown() = Refinement(emptyMap())
        }
    }

    private val knownRefinements: HashMap<Method, Refinement> = hashMapOf()

    override val cm: ClassManager get() = ctx.cm

    override fun cleanup() {}

    override fun visit(method: Method) {
        super.visit(method)
        if (debugMethods.isNotEmpty() && method.name !in debugMethods) return
        getOrComputeRefinement(method)
    }

    fun getOrComputeRefinement(method: Method): Refinement {
        val refinement = knownRefinements[method] ?: analyzeMethod(method)
        knownRefinements[method] = refinement
        return refinement
    }

    private fun analyzeMethod(method: Method) = try {
        analyzeMethodPaths(method)
    } catch (ex: Exception) {
        log.error("Error in analysis: method $method", ex)
        Refinement.unknown()
    }

    private fun getThrowType(inst: ThrowInst): Type = when {
        inst.throwable is CastInst -> (inst.throwable as CastInst).operand.type
        else -> inst.type
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

    private fun findExceptionPaths(method: Method): Map<RefinementCriteria, ChoiceState> {
        val builder = psa.builder(method)
        val instructions = builder.methodExitInstructions()
        return instructions.filterIsInstance<ThrowInst>()
                .map { getThrowType(it) to builder.getInstructionState(it) }
                .filter { it.second != null }
                .map { it.first to it.second!!.filterByType(PredicateType.Path()) }
                .map { RefinementCriteria(it.first) to it.second }
                .groupBy({ it.first }, { it.second })
                .mapValues { (_, values) -> ChoiceState(values) }
    }

    private fun findNormalPaths(method: Method): PredicateState {
        val builder = psa.builder(method)
        val instructions = builder.methodExitInstructions()
        return instructions.filterNot { it is ThrowInst }
                .mapNotNull { builder.getInstructionState(it) }
                .map { it.filterByType(PredicateType.Path()) }
                .let { ChoiceState(it) }
    }

    private fun nestedMethodsExceptions(method: Method): Pair<PredicateState, Map<RefinementCriteria, PredicateState>> {
        val builder = psa.builder(method)
        val calls = MethodCallCollector.calls(cm, method)
        val calledMethods = calls.map { it.method }
        val refinements = calledMethods.map { getOrComputeRefinement(it) }
        val refinementMap = calledMethods.zip(refinements).toMap()
        val states = calls.map { call ->
            (builder.getInstructionState(call) ?: BasicState())
                    .filter { it is CallPredicate || it.type == PredicateType.Path() }
        }
        val result = arrayListOf<Pair<RefinementCriteria, PredicateState>>()
        for ((method, state, refinement) in zip(calledMethods, states, refinements)) {
            val others = refinementMap
                    .filterKeys { it != method }
                    .mapValues { it.value.allPaths().not() }
            for ((target, ref) in refinement.allTargets()) {
                val mapping = others + (method to ref)
                val resultPath = MethodRefinementsInliner(mapping).apply(state)
                result.add(target to resultPath)
            }
        }
        val exceptionalPaths = result
                .groupBy({ it.first }, { it.second })
                .mapValues { (_, values) -> ChoiceState(values) }
        val normalPath = ChoiceState(refinements.map { it.allPaths() }).not()
        return normalPath to exceptionalPaths
    }


    private fun PredicateState.optimize() = transform(this) {
        +ConstantPropagator
        +Optimizer()
    }

    private fun merge(first: Map<RefinementCriteria, PredicateState>, second: Map<RefinementCriteria, PredicateState>
    ): MutableMap<RefinementCriteria, PredicateState> {
        val result = first.toMutableMap()
        for ((k, v) in second) {
            val current = result[k]
            if (current == null) {
                result[k] = v
            } else {
                result[k] = ChoiceState(listOf(current, v))
            }
        }
        return result
    }

    private fun analyzeMethodPaths(method: Method): Refinement {
        log.info("Start analysis: $method")

        val state = methodFullState(method)
        val exceptions = findExceptionPaths(method)
        val normalPaths = findNormalPaths(method)
        val (nestedNormal, nestedExceptions) = nestedMethodsExceptions(method)

        val allExceptions = merge(exceptions, nestedExceptions).mapValues { it.value.optimize() }
        val allNormal = ChainState(normalPaths, nestedNormal).optimize()


        log.info("Analyze: $method")
        log.info("State:\n$state\nExceptions:\n$allExceptions\nNormal:\n$allNormal")

        val (trivialPaths, exceptionPathsToQuery) = searchForDummySolution(allNormal, allExceptions)
        val (queryExceptions, queryPaths) = exceptionPathsToQuery.toList().unzip()
        val answer = queryFixpointSolver(state, allNormal, queryPaths)
        val result = (trivialPaths + queryExceptions.zip(answer)).toMap()

        log.info("Result $method:\n$result")
        return Refinement(result)
    }


    private fun searchForDummySolution(normal: PredicateState, exceptions: Map<RefinementCriteria, PredicateState>
    ): Pair<Map<RefinementCriteria, PredicateState>, Map<RefinementCriteria, PredicateState>> {
        val exceptionPathsToQuery = hashMapOf<RefinementCriteria, PredicateState>()
        val knownPaths = hashMapOf<RefinementCriteria, PredicateState>()
        for ((ex, path) in exceptions.entries) {
            val dummyResult = analyzeForDummyResult(normal, path)
            if (dummyResult != null) {
                knownPaths[ex] = dummyResult
            } else {
                exceptionPathsToQuery[ex] = path
            }
        }
        return knownPaths to exceptionPathsToQuery
    }

    private fun analyzeForDummyResult(normalPaths: PredicateState, exceptionPaths: PredicateState): PredicateState? = when {
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
        else -> null
    }

    private fun queryFixpointSolver(state: PredicateState, normal: PredicateState, exceptions: List<PredicateState>): List<PredicateState> =
            try {
                val result = Z3FixpointSolver(cm.type).mkFixpointQuery(state, exceptions, normal)
                when (result) {
                    is Z3FixpointSolver.FixpointResult.Sat -> result.result
                    else -> exceptions.map { falseState() }
                }
            } catch (ex: Z3FixpointSolver.FixpointQueryException) {
                log.error("Bad fixpoint query: ${ex.status}")
                exceptions.map { falseState() }
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


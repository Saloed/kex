package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.falseState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst

class RecursionAnalyzer(val cm: ClassManager, val psa: PredicateStateAnalysis, val root: Method) {

    private fun methodRecursiveCallTraces(): List<List<CallInst>> {
        fun go(method: Method, methodTrace: List<Method>, trace: List<CallInst>): List<List<CallInst>> =
                when (method) {
                    root -> listOf(trace)
                    in methodTrace -> emptyList()
                    else -> MethodCallCollector.calls(cm, method)
                            .flatMap { go(it.method, methodTrace + listOf(method), trace + listOf(it)) }
                            .filter { it.isNotEmpty() }
                }

        return MethodCallCollector.calls(cm, root)
                .flatMap { go(it.method, listOf(root), listOf(it)) }
                .filter { it.isNotEmpty() }
    }


    fun analyze(): Refinements {
        log.info("Analyze recursive method: $root")
        val recursiveTraces = methodRecursiveCallTraces()
        if (recursiveTraces.any { it.size > 1 }) {
            TODO("Co-recursion is not supported yet")
        }

        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, root)
        val (state, recursiveCalls) = buildMethodState(methodPaths)
        if (recursiveCalls.isEmpty()) {
            throw IllegalArgumentException("No recursive calls to analyze")
        }
        val rootCall = createRootCall()
        val normalExecution = methodPaths.normalExecutionPaths.optimize()
        val recursionPaths = recursiveTraces
                .map { it.last() }
                .mapNotNull { methodPaths.builder.getInstructionState(it) }
                .map { it.filterByType(PredicateType.Path()) }
                .let { ChoiceState(it) }
                .optimize()
        val refinements = methodPaths.refinementSources.value.map {
            computeRefinement(state, rootCall, recursiveCalls, recursionPaths, normalExecution, it)
        }
        return Refinements(refinements)
    }

    private fun computeRefinement(
            state: PredicateState,
            rootCall: CallPredicate,
            recursiveCalls: List<CallPredicate>,
            recursionPaths: PredicateState,
            normalPaths: PredicateState,
            refinementSource: RefinementSource
    ): Refinement {
        val refinementPath = refinementSource.condition.optimize()
        val solver = Z3FixpointSolver(cm.type)
        val refinement: PredicateState = try {
            val result = solver.analyzeRecursion(state, recursiveCalls, rootCall, recursionPaths, refinementPath, normalPaths)
            when (result) {
                is FixpointResult.Sat -> result.result.first()
                else ->  falseState()
            }
        } catch (ex: QueryCheckStatus.FixpointQueryException) {
            log.error("Bad fixpoint query: ${ex.status}")
             falseState()
        }
        return Refinement(refinementSource.criteria, refinement)
    }


    private fun createRootCall(): CallPredicate = state {
        val arguments = root.argTypes.withIndex().map { (index, argType) ->
            term { arg(argType.kexType, index) }
        }
        val returnTerm = term { `return`(root) }
        val owner = when {
            root.isStatic -> term { `class`(root.`class`) }
            else -> term { value(root.`class`.kexType, "owner") }
        }
        val methodCall = term { tf.getCall(root, owner, arguments) }
        returnTerm.call(methodCall)
    } as CallPredicate

    private fun buildMethodState(builder: MethodRefinementSourceAnalyzer): Pair<PredicateState, List<CallPredicate>> {
        val recursiveCallPredicates = mutableListOf<CallPredicate>()
        val state = transform(builder.methodRawFullState()) {
            +MethodFunctionalInliner(psa) {
                if (calledMethod == root) {
                    recursiveCallPredicates.add(it)
                    skip()
                    return@MethodFunctionalInliner
                }
                val state = getStateForInlining() ?: return@MethodFunctionalInliner
                inline(state)
            }
            +IntrinsicAdapter
            +Optimizer()
            +ConstantPropagator
            +BoolTypeAdapter(cm.type)
            +ArrayBoundsAdapter()
            +Optimizer()
        }.let { state -> MemorySpacer(state).apply(state) }
        return state to recursiveCallPredicates
    }

}


package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.state.ChoiceState
import org.jetbrains.research.kex.state.PredicateState
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


    fun analyze() {
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
        val recursionPaths = methodPaths.callInstructions
                .filter { it.method == root }
                .mapNotNull { methodPaths.builder.getInstructionState(it) }
                .map { it.filterByType(PredicateType.Path()) }
                .let { ChoiceState(it) }
                .optimize()
        val refinementSrc = methodPaths.refinementSources.value.first().condition.optimize()
        val result = Z3FixpointSolver(cm.type).analyzeRecursion(state, recursiveCalls, rootCall, recursionPaths, refinementSrc, normalExecution)
        println("$state")
        println("$normalExecution")
        println("$refinementSrc")
        println("$result")
        TODO()
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


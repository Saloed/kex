package org.jetbrains.research.kex.asm.analysis.refinements

import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.state
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.term
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
        val rootCall = createRootCall(recursiveCalls.first())
        val normalExecution = methodPaths.normalExecutionPaths.optimize()
        val refinementSources = methodPaths.refinementSources
        val refinementSrc = refinementSources.value.first().condition.optimize()
        val result = Z3FixpointSolver(cm.type).analyzeRecursion(state, recursiveCalls, rootCall, normalExecution, refinementSrc)
        println("$state")
        println("$normalExecution")
        println("$refinementSrc")
        println("$result")
        TODO()
    }

    private fun createRootCall(callPrototype: CallPredicate): CallPredicate {
        val arguments = root.argTypes.withIndex().map { (index, argType) ->
            term { arg(argType.kexType, index) }
        }
        if (!callPrototype.hasLhv) {
            TODO("Recursive call without result receiver")
        }
        val returnTerm = term { `return`(root) }
        val callTerm = callPrototype.call as CallTerm
        if (!callTerm.isStatic) {
            TODO("Non static recursive call")
        }
        val owner = callTerm.owner
        return state { returnTerm.call(term { tf.getCall(root, owner, arguments) }) } as CallPredicate
    }

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


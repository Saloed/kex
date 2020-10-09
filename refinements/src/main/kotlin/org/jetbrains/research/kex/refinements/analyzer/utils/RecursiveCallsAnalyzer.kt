package org.jetbrains.research.kex.refinements.analyzer.utils

import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst

internal typealias CallStack = List<Pair<CallInst, Method>>

class RecursiveCallsAnalyzer(
        private val mr: MethodRefinements,
        private val cm: ClassManager,
        private val targetMethod: Method,
        private val stack: CallStack = emptyList()
) {
    fun analyze(method: Method): List<CallStack> {
        if (method == targetMethod && stack.isNotEmpty()) return listOf(stack)
        val calls = MethodCallCollector.calls(cm, method)
        return calls.map { analyzeCall(it) }.mergeCallStack()
    }

    private fun analyzeCall(call: CallInst) = when (MethodManager.InlineManager.isInlinable(call.method)) {
        MethodManager.InlineManager.InlineStatus.NO_INLINE -> emptyList()
        MethodManager.InlineManager.InlineStatus.INLINE -> listOf(forceAnalyzeMethod(call.method, call))
        MethodManager.InlineManager.InlineStatus.MAY_INLINE -> MethodImplementations(cm, mr)
                .collectImplementations(call.method)
                .map { forceAnalyzeMethod(it, call) }
    }.mergeCallStack()


    private fun List<List<CallStack>>.mergeCallStack() = filter { it.isNotEmpty() }.flatten()

    private fun forceAnalyzeMethod(method: Method, callInst: CallInst) =
            RecursiveCallsAnalyzer(mr, cm, targetMethod, stack + listOf(callInst to method)).analyze(method)

    companion object {
        fun allRecursiveCallsPlacedInMethodBody(traces: List<CallStack>) = traces.all { it.size == 1 }
        fun recursiveCallInstructions(traces: List<CallStack>) = traces.map { it.last() }
    }
}

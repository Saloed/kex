package org.jetbrains.research.kex.asm.analysis

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.asm.analysis.refinements.MethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.RecursiveMethodAnalyzer
import org.jetbrains.research.kex.asm.analysis.refinements.Refinements
import org.jetbrains.research.kex.asm.analysis.refinements.SimpleMethodAnalyzer
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.visitor.MethodVisitor


class MethodRefinements(
        private val ctx: ExecutionContext,
        private val psa: PredicateStateAnalysis,
        private val debugMethods: List<String> = emptyList()
) : MethodVisitor {

    private val knownRefinements: HashMap<Method, Refinements> = hashMapOf()

    private val methodAnalysisStack = dequeOf<Method>()

    override val cm: ClassManager get() = ctx.cm

    override fun cleanup() {}


    override fun visit(method: Method) {
        super.visit(method)
        if (methodAnalysisStack.isNotEmpty())
            throw IllegalStateException("Method stack must be empty")
        if (debugMethods.isNotEmpty() && method.name !in debugMethods) return
        getOrComputeRefinement(method)
    }

    fun getOrComputeRefinement(method: Method): Refinements {
        val refinement = knownRefinements[method] ?: analyzeMethod(method)
        knownRefinements[method] = refinement
        return refinement
    }

    private fun analyzeMethod(method: Method): Refinements {
        log.info("Start analysis: $method")
        if (method in methodAnalysisStack) {
            knownRefinements[method] = RecursiveMethodAnalyzer(cm, psa, this, method).analyzeSafely()
            throw SkipRecursion(method)
        }
        methodAnalysisStack.addLast(method)
        val result = SimpleMethodAnalyzer(cm, psa, this, method).analyzeSafely()
        methodAnalysisStack.removeLast()
        log.info("Result $method:\n$result")
        return result
    }

    private fun MethodAnalyzer.analyzeAndTrackRecursion() = try {
        analyze()
    } catch (skip: SkipRecursion) {
        if (methodAnalysisStack.isEmpty()) throw IllegalStateException("Empty recursion stack")
        if (methodAnalysisStack.last != skip.method) {
            methodAnalysisStack.removeLast()
            throw skip
        }
        knownRefinements[skip.method] ?: Refinements.unknown(skip.method)
    }

    private fun MethodAnalyzer.analyzeSafely() = try {
        analyzeAndTrackRecursion()
    } catch (ex: Exception) {
        log.error("Error in analysis: method $method", ex)
        Refinements.unknown(method)
    } catch (ex: NotImplementedError) {
        log.error("Error in analysis: method $method", ex)
        Refinements.unknown(method)
    }

    private class SkipRecursion(val method: Method) : Exception() {
        override fun fillInStackTrace() = this
    }

}


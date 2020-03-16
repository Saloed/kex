package org.jetbrains.research.kex.asm.analysis

import com.abdullin.kthelper.collection.dequeOf
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.asm.analysis.refinements.*
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.state.PredicateStateBuilder
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.transformer.MethodFunctionalInliner
import org.jetbrains.research.kex.state.transformer.PredicateCollector
import org.jetbrains.research.kex.state.transformer.optimize
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.visitor.MethodVisitor
import ru.spbstu.ktuples.zip


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
        if (method in methodAnalysisStack) {
            knownRefinements[method] = RecursiveMethodAnalyzer(cm, psa, this, method).analyze()
            throw SkipRecursion(method)
        }
        methodAnalysisStack.addLast(method)
        log.info("Start analysis: $method")

        val result = try {
            SimpleMethodAnalyzer(cm, psa, this, method).analyze()
        } catch (skip: SkipRecursion) {
            if (methodAnalysisStack.isEmpty()) throw IllegalStateException("Empty recursion stack")
            if (methodAnalysisStack.last != skip.method) {
                methodAnalysisStack.removeLast()
                throw skip
            }
            knownRefinements[skip.method] ?: Refinements.unknown(skip.method)
        } catch (ex: Exception) {
            log.error("Error in analysis: method $method", ex)
            Refinements.unknown(method)
        }
        log.info("Result $method:\n$result")

        methodAnalysisStack.removeLast()
        return result
    }

    private class SkipRecursion(val method: Method) : Exception() {
        override fun fillInStackTrace() = this
    }

}


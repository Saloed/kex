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
            knownRefinements[method] = RecursionAnalyzer(cm, psa, method, this).analyze()
            throw SkipRecursion(method)
        }
        methodAnalysisStack.addLast(method)
        log.info("Start analysis: $method")

        val result = try {
            analyzeMethodPaths(method)
        } catch (skip: SkipRecursion) {
            if (methodAnalysisStack.isEmpty()) throw IllegalStateException("Empty recursion stack")
            if (methodAnalysisStack.last != skip.method) {
                methodAnalysisStack.removeLast()
                throw skip
            }
            knownRefinements[skip.method] ?: Refinements.unknown()
        } catch (ex: Exception) {
            log.error("Error in analysis: method $method", ex)
            Refinements.unknown()
        }
        log.info("Result $method:\n$result")

        methodAnalysisStack.removeLast()
        return result
    }

    private class SkipRecursion(val method: Method) : Exception() {
        override fun fillInStackTrace() = this
    }

    private fun nestedMethodCallStates(psb: PredicateStateBuilder, call: CallInst): Pair<PredicateState, Map<CallPredicate, CallInst>> {
        val state = (psb.getInstructionState(call) ?: BasicState())
                .filter { it is CallPredicate || it.type == PredicateType.Path() }
        val callPredicates = PredicateCollector.collectIsInstance<CallPredicate>(state)
        val callInstructions = callPredicates.map {
            psb.findInstructionsForPredicate(it) as? CallInst
                    ?: throw IllegalStateException("Cant find instruction for call")
        }
        val callMap = callPredicates.zip(callInstructions).toMap()
        return state to callMap
    }

    fun nestedMethodsExceptions(method: Method, ignoredCalls: List<CallInst> = emptyList()): Pair<NegationState, RefinementSources> {
        val builder = psa.builder(method)
        val calls = MethodCallCollector.calls(cm, method).filterNot { it in ignoredCalls }
        val refinements = calls.map { getOrComputeRefinement(it.method) }
        val refinementMap = calls.zip(refinements).toMap()
        val result = arrayListOf<RefinementSource>()
        for ((call, refinement) in zip(calls, refinements)) {
            val otherCalls = refinementMap
                    .filterKeys { it != call }
                    .mapValues { it.value.allStates().not() }
            val (state, callInstructions) = nestedMethodCallStates(builder, call)
            for ((criteria, refState) in refinement.expanded().value) {
                val mapping = otherCalls + (call to refState)
                val inliner = MethodFunctionalInliner(psa) { predicate ->
                    val instruction = callInstructions[predicate]
                            ?: throw IllegalStateException("No instruction for predicate")
                    if (instruction in ignoredCalls) {
                        skip()
                        return@MethodFunctionalInliner
                    }
                    val predicateState = mapping[instruction]
                            ?: throw IllegalArgumentException("No method $predicate for inline")
                    inline(predicateState)
                }
                val resultPath = inliner.apply(state)
                result.add(RefinementSource(criteria, resultPath))
            }
        }
        val exceptionalPaths = RefinementSources(result).simplify()
        val normalPath = ChoiceState(refinements.map { it.allStates() }).not()
        return normalPath to exceptionalPaths
    }


    private fun analyzeMethodPaths(method: Method): Refinements {
        val methodPaths = MethodRefinementSourceAnalyzer(cm, psa, method)
        val state = methodPaths.fullState
        val refinementSources = methodPaths.refinementSources
        val normalPaths = methodPaths.normalExecutionPaths
        val (nestedNormal, nestedRefinementSources) = nestedMethodsExceptions(method)

        val allSources = refinementSources.merge(nestedRefinementSources)
        val allNormal = ChainState(normalPaths, nestedNormal).optimize()

        log.info("Analyze: $method")
        log.info("State:\n$state\nExceptions:\n$allSources\nNormal:\n$allNormal")

        val (trivialRefinements, sourcesToQuery) = searchForDummySolution(allNormal, allSources)
        val otherRefinements = queryRefinementSources(state, allNormal, sourcesToQuery)

        return Refinements(trivialRefinements.value + otherRefinements.value)
    }

    private fun searchForDummySolution(normal: PredicateState, exceptions: RefinementSources): Pair<Refinements, RefinementSources> {
        val sourcesToQuery = mutableListOf<RefinementSource>()
        val dummyRefinements = mutableListOf<Refinement>()
        for (source in exceptions.value) {
            val dummyResult = analyzeForDummyResult(normal, source.condition)
            if (dummyResult == null) {
                sourcesToQuery.add(source)
                continue
            }
            dummyRefinements.add(Refinement(source.criteria, dummyResult))
        }
        return Refinements(dummyRefinements) to RefinementSources(sourcesToQuery)
    }

    private fun analyzeForDummyResult(normalPaths: PredicateState, exceptionPaths: PredicateState): PredicateState? = when {
        normalPaths.evaluatesToTrue && exceptionPaths.evaluatesToFalse -> falseState()
        normalPaths.evaluatesToFalse && exceptionPaths.evaluatesToTrue -> trueState()
        normalPaths.evaluatesToTrue && exceptionPaths.evaluatesToTrue -> {
            log.error("Normal and Exception paths are always true")
            falseState()
        }
        normalPaths.evaluatesToFalse && exceptionPaths.evaluatesToFalse -> {
            log.error("Normal and Exception paths are always false")
            falseState()
        }
        else -> null
    }

    private fun queryRefinementSources(state: PredicateState, normal: PredicateState, sources: RefinementSources): Refinements {
        val conditions = sources.value.map { it.condition }
        val fixpointAnswer = queryFixpointSolver(state, normal, conditions)
        val refinements = sources.value.zip(fixpointAnswer).map { (src, answer) -> Refinement(src.criteria, answer) }
        return Refinements(refinements)
    }

    private fun queryFixpointSolver(state: PredicateState, normal: PredicateState, exceptions: List<PredicateState>): List<PredicateState> =
            try {
                val result = Z3FixpointSolver(cm.type).mkFixpointQuery(state, exceptions, normal)
                when (result) {
                    is FixpointResult.Sat -> result.result
                    else -> exceptions.map { falseState() }
                }
            } catch (ex: QueryCheckStatus.FixpointQueryException) {
                log.error("Bad fixpoint query: ${ex.status}")
                exceptions.map { falseState() }
            }

}


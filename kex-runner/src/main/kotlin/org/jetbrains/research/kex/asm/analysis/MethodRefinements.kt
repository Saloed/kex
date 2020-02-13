package org.jetbrains.research.kex.asm.analysis

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.ktype.KexPointer
import org.jetbrains.research.kex.smt.AbstractSMTSolver
import org.jetbrains.research.kex.smt.Result
import org.jetbrains.research.kex.smt.SMTProxySolver
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateBuilder
import org.jetbrains.research.kex.state.predicate.PredicateType
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.*
import org.jetbrains.research.kex.util.info
import org.jetbrains.research.kex.util.log
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode
import org.jetbrains.research.kfg.ir.value.instruction.Instruction
import org.jetbrains.research.kfg.ir.value.instruction.ThrowInst
import org.jetbrains.research.kfg.ir.value.instruction.UnreachableInst
import org.jetbrains.research.kfg.type.*
import org.slf4j.LoggerFactory
import java.util.*
import kotlin.collections.HashMap

object MethodRefinements {
    private val refinements = HashMap<Method, List<Refinement>>()

    fun add(
            method: Method,
            state: PredicateState,
            path: PredicateState,
            exception: Throwable? = null
    ) {
        val methodPath = MethodPath(state, path)
        val refinement = when (exception) {
            null -> Refinement.RefinementNoException(methodPath)
            else -> Refinement.RefinementException(methodPath, exception)
        }
        refinements[method] = refinements.getOrDefault(method, emptyList()) + refinement
    }

    sealed class Refinement(val path: MethodPath) {
        class RefinementException(
                path: MethodPath,
                val exception: Throwable
        ) : Refinement(path)

        class RefinementNoException(
                path: MethodPath
        ) : Refinement(path)
    }

    data class MethodRefinement(
            val method: Method,
            val noException: List<MethodPath>,
            val exception: List<MethodPath>
    )

    data class MethodPath(val state: PredicateState, val path: PredicateState)

    private fun List<MethodPath>.mergePaths(): MethodPath {
        val states = map { it.state }.asChoice().simplify()
        val paths = map { it.path }.asChoice().simplify()
        return MethodPath(states, paths)
    }

    private fun Collection<PredicateState>.asChoice() = filter { it.isNotEmpty }.run {
        when (size) {
            0 -> BasicState()
            1 -> first()
            else -> ChoiceState(this.toList())
        }
    }

    fun getRefinements(psa: PredicateStateAnalysis): Map<Method, MethodRefinement> {
        val result = HashMap<Method, MethodRefinement>()
        for ((method, refinements) in refinements.entries) {
            val noException = refinements.filterIsInstance<Refinement.RefinementNoException>()
                    .map { it.path }
            val exception = refinements.filterIsInstance<Refinement.RefinementException>()
                    .map { it.path }
            result[method] = MethodRefinement(method, noException, exception)
        }
        result.entries.map { (_, refinement) ->
            analyzeMethod(refinement, psa)
        }
        return result
    }

    private fun getTruePs() = BasicState()
    private val predicateCandidatesBuilder = PredicateBuilder.Assume()

    private fun PredicateBuilder.generateCandidates(lhs: Term, rhs: Term) = listOf(
            lhs ge rhs equality true,
            lhs le rhs equality true,
            lhs neq rhs equality true,
            lhs eq rhs equality true
    )

    fun predicateIsPossible(solver: AbstractSMTSolver, predicate: Predicate, cm: ClassManager): Boolean {
        if (predicate !is EqualityPredicate) return false
        if (!termIsPossible(predicate.lhv, cm) || !termIsPossible(predicate.rhv, cm)) return false
        try {
            val ps = BasicState(listOf(predicate))
            solver.isViolated(ps, getTruePs())
            return true
        } catch (ex: IllegalStateException) {
            return false
        }
    }

    fun termIsPossible(term: Term, cm: ClassManager): Boolean {
        if (term is CmpTerm && term.lhv.type != term.rhv.type) {
            if (term.lhv.type !is KexPointer || term.rhv.type !is KexPointer) {
                return false
            }
            if (term.opcode !is CmpOpcode.Eq && term.opcode !is CmpOpcode.Neq) {
                return false
            }
            val lType = term.lhv.type.getKfgType(cm.type)
            val rType = term.rhv.type.getKfgType(cm.type)
            return checkReferenceTypes(lType, rType)
        }
        return true
    }

    private fun checkReferenceTypes(lType: Type, rType: Type) = when {
        lType !is Reference || rType !is Reference -> false
        lType == rType -> true
        lType is NullType || rType is NullType -> true
        lType is ArrayType && rType is ArrayType -> checkArraySubtyping(lType, rType)
        lType is ClassType && rType is ClassType -> checkClassSubtyping(lType, rType)
        // todo: maybe more checks
        else -> false
    }

    private fun checkClassSubtyping(lType: ClassType, rType: ClassType) = when {
        // fixme: tricky hack with OuterClass
        lType.`class` is OuterClass && rType.`class` is OuterClass -> true
        lType.`class` is OuterClass -> rType.`class`.isAncestor(lType.`class`)
        rType.`class` is OuterClass -> lType.`class`.isAncestor(rType.`class`)
        else -> lType.`class`.isAncestor(rType.`class`) || rType.`class`.isAncestor(lType.`class`)
    }

    private fun checkArraySubtyping(lType: ArrayType, rType: ArrayType): Boolean = when {
        lType.component == rType.component -> true
        lType.component.isReference && rType.component.isReference -> {
            checkReferenceTypes(lType.component, rType.component)
        }
        else -> false
    }

    fun predicateIsApplicable(predicates: Set<Predicate>, predicate: Predicate): Boolean {
        if (predicate !is EqualityPredicate) return true
        val cmpTerms = predicates.filterIsInstance<EqualityPredicate>()
                .flatMap { listOf(it.lhv, it.rhv) }
                .filterIsInstance<CmpTerm>()
        if (predicate.lhv is CmpTerm && !cmpTermIsApplicable(cmpTerms, predicate.lhv as CmpTerm)) return false
        if (predicate.rhv is CmpTerm && !cmpTermIsApplicable(cmpTerms, predicate.rhv as CmpTerm)) return false
        return true
    }

    private fun cmpTermIsApplicable(terms: List<CmpTerm>, term: CmpTerm): Boolean {
        val termToCheck = terms.filter { it.lhv == term.lhv && it.rhv == term.rhv }
        return when (term.opcode) {
            is CmpOpcode.Eq -> termToCheck.none {
                it.opcode is CmpOpcode.Eq
                        || it.opcode is CmpOpcode.Neq
                        || it.opcode is CmpOpcode.Le
                        || it.opcode is CmpOpcode.Ge
            }
            is CmpOpcode.Neq -> termToCheck.none {
                it.opcode is CmpOpcode.Neq || it.opcode is CmpOpcode.Eq
            }
            is CmpOpcode.Le -> termToCheck.none {
                it.opcode is CmpOpcode.Ge
            }
            is CmpOpcode.Ge -> termToCheck.none {
                it.opcode is CmpOpcode.Le
            }
            else -> true
        }
    }

    private fun PredicateBuilder.possibleFields(
            variable: Term,
            positive: PredicateState,
            negative: PredicateState,
            cm: ClassManager
    ): List<Term> {
        if (variable.type !is KexPointer) return emptyList()
        val variableType = variable.type.getKfgType(cm.type)
        val fieldCollector = TermCollector {
            it is FieldTerm && checkReferenceTypes(variableType, it.owner.type.getKfgType(cm.type))
        }
        fieldCollector.transform(positive)
        fieldCollector.transform(negative)
        return fieldCollector.terms
                .filterIsInstance<FieldTerm>()
                .map { FieldTerm(it.type, variable, it.fieldName) }
                .map { it.load() }
    }

    private fun generatePossiblePredicates(
            variable: Term,
            solver: AbstractSMTSolver,
            positive: PredicateState,
            negative: PredicateState,
            cm: ClassManager
    ): List<Predicate> {
        val collector = TermCollector { it.isConst || it is ArgumentTerm && it != variable }
        collector.transform(positive)
        collector.transform(negative)
        val argumentTerms = collector.terms + setOf(
                TermFactory.getConstant(0), TermFactory.getNull())
        val candidates = argumentTerms
                .flatMap { predicateCandidatesBuilder.generateCandidates(variable, it) }
                .filter { predicateIsPossible(solver, it, cm) }
        val possibleFields = predicateCandidatesBuilder.possibleFields(variable, positive, negative, cm)
        val fieldCandidates = possibleFields.allCombinationsWith(argumentTerms)
                .flatMap { (field, argument) ->
                    predicateCandidatesBuilder.generateCandidates(field, argument)
                }
                .filter { predicateIsPossible(solver, it, cm) }
        return candidates + fieldCandidates
    }


    private fun <T1, T2> Iterable<T1>.allCombinationsWith(other: Iterable<T2>) =
            flatMap { first -> other.map { first to it } }

    class PredicateAbstractionState(val variables: List<Term>, val cm: ClassManager) {


        private fun generateCandidatePredicates(
                solver: AbstractSMTSolver,
                positive: List<MethodPath>,
                negative: List<MethodPath>
        ): Set<Predicate> {
            val positiveState = positive.mergePaths().state
            val negativeState = negative.mergePaths().state
            return variables.flatMap { variable ->
                generatePossiblePredicates(variable, solver, positiveState, negativeState, cm)
            }.toSet()
        }


        class GeneratedPredicate(
                val ps: BasicState,
                private val candidatePredicates: Set<Predicate>
        ) {

            private val predicateSet = ps.predicates.toSet()

            fun nextCandidates(): Set<GeneratedPredicate> {
                val possible = candidatePredicates.filter { predicateIsApplicable(predicateSet, it) }.toSet()
                return possible.map {
                    GeneratedPredicate(ps.addPredicate(it), possible - it)
                }.toSet()
            }

            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is GeneratedPredicate) return false
                if (predicateSet != other.predicateSet) return false
                return true
            }

            override fun hashCode(): Int {
                return predicateSet.hashCode()
            }
        }


        fun makeAbstraction(
                solver: AbstractSMTSolver,
                refinement: MethodRefinement,
                psa: PredicateStateAnalysis,
                positive: List<MethodPath>,
                negative: List<MethodPath>
        ): PredicateState? {
            if (positive.isEmpty() && negative.isEmpty()) {
                log.info("Empty paths")
                return null
            }

            val candidates = generateCandidatePredicates(solver, positive, negative)
            log.info("Number of candidates: {}", candidates.size)
            log.info(BasicState(candidates.toList()))

            val state = methodFullState(refinement.method, psa)

            val positivePaths = ChoiceState(positive.map { it.path }).simplify()
            val negativePaths = ChoiceState(negative.map { it.path }).simplify()

            val positivePath = when {
                positive.isNotEmpty() -> positivePaths
                else -> !negativePaths
            }
            val negativePath = when {
                negative.isNotEmpty() -> negativePaths
                else -> !positivePaths
            }

            log.info("State\n{}", state)
            log.info("Positive path\n{}", positivePath)
            log.info("Negative path\n{}", negativePath)

            val checkedPredicates = mutableSetOf<GeneratedPredicate>()
            val predicateQueue = ArrayDeque<GeneratedPredicate>()
            predicateQueue.add(GeneratedPredicate(BasicState(), candidates))

            while (predicateQueue.isNotEmpty()) {
                val current = predicateQueue.poll()
                if (current in checkedPredicates) continue
                checkedPredicates.add(current)

                log.info(current.ps)

                val checkState = current.ps + state

                solver.isPathPossible(checkState, positivePath) as? Result.SatResult
                        ?: continue

                when (solver.isPathPossible(checkState, negativePath)) {
                    is Result.UnsatResult -> return current.ps
                    is Result.SatResult -> {
                        predicateQueue.addAll(current.nextCandidates())
                    }
                }
            }

            return null
        }
    }

    private operator fun AbstractSMTSolver.invoke(
            paths: List<MethodPath>,
            fn: AbstractSMTSolver.(MethodPath) -> Result
    ) = paths.asSequence().map { fn(it) }

    private fun methodArguments(refinement: MethodRefinement): Set<Term> {
        val exceptionState = refinement.exception.mergePaths().state
        val noExceptionState = refinement.noException.mergePaths().state
        val argumentsCollector = TermCollector { it is ArgumentTerm }
        argumentsCollector.transform(exceptionState)
        argumentsCollector.transform(noExceptionState)
        return argumentsCollector.terms
    }

    fun chainWithNegation(base: PredicateState, curr: PredicateState) = when {
        curr.isEmpty -> base
        else -> ChainState(base, !curr)
    }.simplify()

    fun coveredBasicBlocks(inst: Instruction): Set<BasicBlock> {
        val active = hashSetOf<BasicBlock>()
        val queue = ArrayDeque<BasicBlock>()
        queue.push(inst.parent!!)
        while (queue.isNotEmpty()) {
            val current = queue.first
            if (current !in active) {
                active.add(current)
                queue.addAll(current.predecessors)
            }
            queue.pop()
        }
        return active
    }

    fun uncoveredBasicBlocks(blocks: List<BasicBlock>, inst: Instruction): List<BasicBlock> {
        val covered = coveredBasicBlocks(inst)
        return blocks.filterNot { it in covered }
    }

    fun methodExitInstructions(method: Method): List<Instruction> {
        val instructions = arrayListOf<Instruction>()
        var blocks = method.toList()
        while (blocks.isNotEmpty()) {
            val inst = blocks.flatten()
                    .dropLastWhile { it is UnreachableInst }
                    .lastOrNull()
                    ?: return emptyList()
            instructions.add(inst)
            blocks = uncoveredBasicBlocks(blocks, inst)
        }
        return instructions
    }

    fun methodFullState(method: Method, psa: PredicateStateAnalysis): PredicateState {
        val builder = psa.builder(method)
        val instructions = methodExitInstructions(method)
        val states = instructions.mapNotNull { builder.getInstructionState(it) }
        var state: PredicateState = ChoiceState(states)
        state = MethodInliner(method, psa).apply(state)
        state = IntrinsicAdapter.apply(state)
        state = Optimizer().apply(state)
        state = ConstantPropagator.apply(state)
        state = BoolTypeAdapter(method.cm.type).apply(state)
        state = ArrayBoundsAdapter().apply(state)

        state = MemorySpacer(state).apply(state)
        state = Optimizer().apply(state)
        return state
    }

    fun findExceptionRelatedPaths(method: Method, psa: PredicateStateAnalysis): Pair<List<PredicateState>, List<PredicateState>> {
        val builder = psa.builder(method)
        val instructions = methodExitInstructions(method)
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


    fun methodPathsForFixpoint(refinement: MethodRefinement, psa: PredicateStateAnalysis) {
        val state = methodFullState(refinement.method, psa)
        val (normalPaths, exceptionPaths) = findExceptionRelatedPaths(refinement.method, psa)

        val arguments = methodArguments(refinement)
        if (arguments.isEmpty()) return
        log.info("Start fixpoint: ${refinement.method.name}")
        log.info("$refinement")


        val allExceptions = ChoiceState(exceptionPaths)
        val allNormal = ChoiceState(normalPaths)

        val slv = Z3FixpointSolver(refinement.method.cm.type)
        slv.mkFixpointStatement(state, allExceptions, allNormal)
        val a = 3

    }

    fun analyzeMethod(refinement: MethodRefinement, psa: PredicateStateAnalysis) {
        if (refinement.method.name.endsWith("dummy2").not()) {
            return
        }

        methodPathsForFixpoint(refinement, psa)

        return

        val arguments = methodArguments(refinement)
        if (arguments.isEmpty()) return
        val solver = SMTProxySolver(refinement.method.cm.type).solver
        log.info("Start abstraction: ${refinement.method.name}")
        log.info("$refinement")

        val abstraction = PredicateAbstractionState(arguments.toList(), refinement.method.cm)
        val result = abstraction.makeAbstraction(
                solver,
                refinement,
                psa,
                refinement.noException.filter { it.state.isNotEmpty },
                refinement.exception.filter { it.state.isNotEmpty }
        )
        when {
            result != null -> log.info("Find abstraction: $result")
            else -> log.info("abstraction not found")
        }

    }

    private inline fun withDebug(body: () -> Unit) {
        val logger = LoggerFactory.getLogger("org.jetbrains.research") as Logger
        val levelBefore = logger.level
        logger.level = Level.ALL
        body()
        logger.level = levelBefore
    }

}

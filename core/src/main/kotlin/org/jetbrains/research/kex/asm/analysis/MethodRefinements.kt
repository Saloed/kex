package org.jetbrains.research.kex.asm.analysis

import org.jetbrains.research.kex.ktype.KexPointer
import org.jetbrains.research.kex.smt.AbstractSMTSolver
import org.jetbrains.research.kex.smt.Result
import org.jetbrains.research.kex.smt.SMTProxySolver
import org.jetbrains.research.kex.state.*
import org.jetbrains.research.kex.state.predicate.EqualityPredicate
import org.jetbrains.research.kex.state.predicate.Predicate
import org.jetbrains.research.kex.state.predicate.PredicateBuilder
import org.jetbrains.research.kex.state.term.*
import org.jetbrains.research.kex.state.transformer.TermCollector
import org.jetbrains.research.kex.util.info
import org.jetbrains.research.kex.util.log
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode

object MethodRefinements {
    val refinements = HashMap<Method, List<Refinement>>()

    fun add(method: Method, ps: PredicateState, exception: Throwable? = null) {
        val refinement = when (exception) {
            null -> MethodRefinements.Refinement.RefinementNoException(ps)
            else -> MethodRefinements.Refinement.RefinementException(ps, exception)
        }
        refinements[method] = refinements.getOrDefault(method, emptyList()) + refinement
    }

    sealed class Refinement(val ps: PredicateState) {
        class RefinementException(ps: PredicateState, val exception: Throwable) : Refinement(ps)
        class RefinementNoException(ps: PredicateState) : Refinement(ps)
    }

    data class MethodRefinement(val noException: PredicateState, val exception: PredicateState)

    private fun Collection<PredicateState>.asChoice() = filter { it.isNotEmpty }.run {
        when (size) {
            0 -> BasicState()
            1 -> first()
            else -> ChoiceState(this.toList())
        }
    }

    fun getRefinements(): Map<Method, MethodRefinement> {
        val result = HashMap<Method, MethodRefinement>()
        for ((method, refinements) in refinements.entries) {
            val noException = refinements.filterIsInstance<Refinement.RefinementNoException>()
            val exception = refinements.filterIsInstance<Refinement.RefinementException>()
            val noExceptionPs = noException.map { it.ps.simplify() }.toSet().asChoice()
            val exceptionPs = exception.map { it.ps.simplify() }.toSet().asChoice()
            val refinement = MethodRefinement(noExceptionPs, exceptionPs)
            analyzeMethod(method, refinement)
            result[method] = refinement
        }
        return result
    }


    class PredicateAbstractionState(val variables: List<Term>) {

        private fun getTruePs() = BasicState()

        val stateBuilder = PredicateBuilder.State()

        private fun PredicateBuilder.generateCandidates(lhs: Term, rhs: Term) = listOf(
                lhs ge rhs equality true,
                lhs le rhs equality true,
                lhs neq rhs equality true,
                lhs eq rhs equality true
        )

        fun predicateIsPossible(solver: AbstractSMTSolver, predicate: Predicate): Boolean {
            if (predicate !is EqualityPredicate) return false
            if (!termIsPossible(predicate.lhv) || !termIsPossible(predicate.rhv)) return false
            try {
                val ps = BasicState(listOf(predicate))
                solver.isViolated(ps, getTruePs())
                return true
            } catch (ex: IllegalStateException) {
                return false
            }
        }

        fun termIsPossible(term: Term): Boolean {
            if (term is CmpTerm && term.lhv.type != term.rhv.type) {
                if (term.lhv.type !is KexPointer || term.rhv.type !is KexPointer) {
                    return false
                }
                if (term.opcode !is CmpOpcode.Eq && term.opcode !is CmpOpcode.Neq) {
                    return false
                }
                // todo: check subtyping somehow
                return true
            }
            return true
        }

        fun predicateIsApplicable(predicates: Set<Predicate>, predicate: Predicate): Boolean {
            if (predicate !is EqualityPredicate) return true
            val cmpTerms = predicates.filterIsInstance<EqualityPredicate>()
                    .flatMap { listOf(it.lhv, it.rhv) }
                    .filterIsInstance<CmpTerm>()
            if (predicate.lhv is CmpTerm && !cmpTermIsApplicable(cmpTerms, predicate.lhv)) return false
            if (predicate.rhv is CmpTerm && !cmpTermIsApplicable(cmpTerms, predicate.rhv)) return false
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

        private fun generateCandidatePredicates(solver: AbstractSMTSolver, positive: PredicateState, negative: PredicateState) =
                variables.flatMap { variable ->
                    val collector = TermCollector { it.isConst || it is ArgumentTerm && it != variable }
                    collector.transform(positive)
                    collector.transform(negative)
                    val argumentTerms = collector.terms + setOf(
                            TermFactory.getConstant(0), TermFactory.getNull())
                    argumentTerms
                            .flatMap { stateBuilder.generateCandidates(variable, it) }
                            .filter { predicateIsPossible(solver, it) }
                }

        fun makeAbstraction(solver: AbstractSMTSolver, positive: PredicateState, negative: PredicateState): PredicateState? {
            val candidates = generateCandidatePredicates(solver, positive, negative)
            log.info("Number of candidates: {}", candidates.size)
            log.info(BasicState(candidates))

            val checkedPredicates = mutableSetOf<Set<Predicate>>()

            fun visit(current: Set<Predicate>, other: List<Predicate>): PredicateState? {
                if (current in checkedPredicates) return null
                checkedPredicates.add(current)
                val ps = BasicState(current.toList())
                val isPossible = solver.isViolated(ps, getTruePs())
                if (isPossible !is Result.SatResult) {
                    return null
                }
                val checkPositive = positive.isEmpty || solver.isViolated(ps, positive.negate()) is Result.UnsatResult
                val checkNegative = negative.isEmpty || solver.isViolated(ps, negative) is Result.UnsatResult

//                log.debug("Positive: {} Negative: {}", positive.negate(), negative)
//                log.debug("Call results: {} {} | {}", checkPositive, checkNegative, ps)

                if (checkPositive && checkNegative) {
//                    log.debug("Always ok")
                    return ps
                }

                // todo: make something on other branches

                for (item in other.filter { predicateIsApplicable(current, it) }) {
                    val newOther = other - item
                    val newCurrent = current + item
                    val result = visit(newCurrent, newOther)
                    if (result != null) {
//                        log.debug("Eeeee, we found smth $result")
                        return result
                    }
                }
                return null
            }

            return visit(emptySet(), candidates)
        }
    }

    fun analyzeMethod(method: Method, refinement: MethodRefinement) {
        val argumentsCollector = TermCollector { it is ArgumentTerm }
        argumentsCollector.transform(refinement.exception)
        argumentsCollector.transform(refinement.noException)
        val arguments = argumentsCollector.terms
        if (arguments.isEmpty()) return
        val solver = SMTProxySolver(method.cm.type).solver
        log.info("Start abstraction: ${method.name}")
        log.info("$refinement")
        val abstraction = PredicateAbstractionState(arguments.toList())
        val result = abstraction.makeAbstraction(solver, refinement.noException, refinement.exception)
        when {
            result != null -> log.info("Find abstraction: $result")
            else -> log.info("abstraction not found")
        }
    }

}

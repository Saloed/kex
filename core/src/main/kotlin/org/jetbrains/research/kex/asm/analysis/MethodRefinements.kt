package org.jetbrains.research.kex.asm.analysis

import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexPointer
import org.jetbrains.research.kex.ktype.KexReference
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
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass
import org.jetbrains.research.kfg.ir.value.instruction.CmpOpcode
import org.jetbrains.research.kfg.type.*

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


    class PredicateAbstractionState(val variables: List<Term>, val cm: ClassManager) {

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

        private fun PredicateBuilder.possibleFields(variable: Term, positive: PredicateState, negative: PredicateState): List<Term> {
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

        private fun generateCandidatePredicates(solver: AbstractSMTSolver, positive: PredicateState, negative: PredicateState) =
                variables.flatMap { variable ->
                    val collector = TermCollector { it.isConst || it is ArgumentTerm && it != variable }
                    collector.transform(positive)
                    collector.transform(negative)
                    val argumentTerms = collector.terms + setOf(
                            TermFactory.getConstant(0), TermFactory.getNull())
                    val candidates = argumentTerms
                            .flatMap { stateBuilder.generateCandidates(variable, it) }
                            .filter { predicateIsPossible(solver, it) }
                    val possibleFields = stateBuilder.possibleFields(variable, positive, negative)
                    val fieldCandidates = possibleFields.allCombinationsWith(argumentTerms)
                            .flatMap { (field, argument) ->
                                stateBuilder.generateCandidates(field, argument)
                            }
                            .filter { predicateIsPossible(solver, it) }
                    (candidates + fieldCandidates).toSet()
                }

        private fun <T1, T2> Iterable<T1>.allCombinationsWith(other: Iterable<T2>) =
                flatMap { first -> other.map { first to it } }

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
        val abstraction = PredicateAbstractionState(arguments.toList(), method.cm)
        val result = abstraction.makeAbstraction(solver, refinement.noException, refinement.exception)
        when {
            result != null -> log.info("Find abstraction: $result")
            else -> log.info("abstraction not found")
        }
    }

}

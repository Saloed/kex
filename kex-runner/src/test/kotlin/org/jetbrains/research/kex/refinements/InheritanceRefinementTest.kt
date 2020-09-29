package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.choice
import org.jetbrains.research.kex.state.emptyState
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.transformer.withMemspace
import kotlin.test.Ignore
import kotlin.test.Test

class InheritanceRefinementTest : RefinementTest("Inheritance") {

    fun String.kexClass() = KexClass(this)

    val positiveCheck = nestedClass("PositiveCheck").kexClass()
    val negativeCheck = nestedClass("NegativeCheck").kexClass()
    val positiveChecker = nestedClass("PositiveChecker").kexClass()
    val checker = nestedClass("Checker").kexClass()

    @Test
    fun testInterfaceInliningKnownType() = run("interfaceInliningKnownType") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 1) ge const(0) equality const(true)
                }
            }
        }
    }

    @Test
    fun testInterfaceInliningSingleCandidate() = run("interfaceInliningSingleCandidate") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 1) ge const(0) equality const(true)
                }
            }
        }
    }

    @Test
    fun testInterfaceInliningManyCandidatesNoResultDependency() = run("interfaceInliningManyCandidatesNoResultDependency") {
        refinement(IllegalArgumentException()) {
            choice({
                path {
                    (arg(checker, 0) `is` positiveCheck) equality const(true)
                }
                path {
                    arg(KexInt(), 1) gt const(0) equality const(true)
                }
            }, {
                path {
                    (arg(checker, 0) `is` negativeCheck) equality const(true)
                }
                path {
                    arg(KexInt(), 1) lt const(0) equality const(true)
                }
            }).withMemoryVersions()
        }
    }

    @Test
    fun testInterfaceInliningManyCandidates() = run("interfaceInliningManyCandidates") {
        refinement(IllegalArgumentException()) {
            choice({
                path {
                    arg(KexInt(), 1) eq const(0) equality const(true)
                }
            }, {
                path {
                    (arg(checker, 0) `is` positiveCheck) equality const(true)
                }
                path {
                    arg(KexInt(), 1) ge const(0) equality const(true)
                }
            }, {
                path {
                    (arg(checker, 0) `is` negativeCheck) equality const(true)
                }
                path {
                    arg(KexInt(), 1) le const(0) equality const(true)
                }
            }).withMemoryVersions()
        }
    }

    val myList = nestedClass("MyList").kexClass()
    val myListA = nestedClass("MyListA").kexClass()
    val myListA1 = nestedClass("MyListA1").kexClass()
    val myListA2 = nestedClass("MyListA2").kexClass()
    val myListB = nestedClass("MyListB").kexClass()
    val myListB1 = nestedClass("MyListB1").kexClass()
    val myListB2 = nestedClass("MyListB2").kexClass()


    @Ignore
    @Test
    fun testFieldAccess() = run("testFieldAccess") {
        refinement(IllegalStateException()) {
            emptyState()
        }
    }

    @Test
    fun testManyExceptionsSource() = run("first") {
        refinement(IllegalArgumentException()) {
            emptyState()
        }
        refinement(IllegalStateException()) {
            emptyState()
        }
    }

    @Test
    fun testManyInterfaceImplsManyExceptions() = run("manyInterfaceImpls1") {
        refinement(IllegalArgumentException()) {
            emptyState()
        }
        refinement(IllegalStateException()) {
            emptyState()
        }
    }

    @Test
    fun testSingleExceptionSource() = run("exceptionIfEmpty") {
        refinement(IllegalArgumentException()) {
            val argument = arg(myList, 0)
            choice({
                path {
                    (argument `is` myListA) or (argument `is` myListA1) or (argument `is` myListA2) equality const(true)
                }
                path {
                    argument.field(KexInt(), "size", myListA).load() equality const(0)
                }
            }, {
                path {
                    argument `is` myListB1 equality const(true)
                }
                path {
                    argument.field(KexInt(), "amount", myListB1).load() equality const(0)
                }
            }, {
                path {
                    argument `is` myListB2 equality const(true)
                }
                path {
                    argument.field(KexInt(), "size", myListB2).load() equality const(0)
                }
            }).withMemoryVersions()
        }
    }

    @Test
    fun testManyInterfaceImplsSingleException() = run("manyInterfaceImpls2") {
        refinement(IllegalArgumentException()) {
            val argument = arg(myList, 0)
            choice({
                path {
                    (argument `is` myListA) or (argument `is` myListA1) or (argument `is` myListA2) equality const(true)
                }
                path {
                    argument.field(KexInt(), "size", myListA).load() equality const(0)
                }
            }, {
                path {
                    argument `is` myListB1 equality const(true)
                }
                path {
                    argument.field(KexInt(), "amount", myListB1).load() equality const(0)
                }
            }, {
                path {
                    argument `is` myListB2 equality const(true)
                }
                path {
                    argument.field(KexInt(), "size", myListB2).load() equality const(0)
                }
            }).withMemoryVersions()
        }
    }

}

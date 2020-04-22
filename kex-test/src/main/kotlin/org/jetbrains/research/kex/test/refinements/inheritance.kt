package org.jetbrains.research.kex.test.refinements

object Inheritance {
    interface Checker {
        fun check(a: Int): Int
    }

    interface PositiveChecker : Checker
    interface NegativeChecker : Checker

    class PositiveCheck : PositiveChecker {
        override fun check(a: Int): Int {
            if (a > 0) throw IllegalArgumentException("Positive check")
            return a
        }
    }

    class NegativeCheck : NegativeChecker {
        override fun check(a: Int): Int {
            if (a < 0) throw IllegalArgumentException("Negative check")
            return a
        }
    }

    fun interfaceInliningKnownType(checker: PositiveCheck, x: Int): Int {
        val res = checker.check(x)
        if (res == 0) throw IllegalArgumentException("Zero")
        return res
    }

    fun interfaceInliningSingleCandidate(checker: PositiveChecker, x: Int): Int {
        val res = checker.check(x)
        if (res == 0) throw IllegalArgumentException("Zero")
        return res
    }

    fun interfaceInliningManyCandidates(checker: Checker, x: Int): Int {
        val res = checker.check(x)
        if (res == 0) throw IllegalArgumentException("Zero")
        return res
    }

    fun interfaceInliningManyCandidatesNoResultDependency(checker: Checker, x: Int): Int {
        checker.check(x)
        return 0
    }

    interface MyList {
        fun isEmpty(): Boolean
        fun get(idx: Int): Int
    }

    abstract class MyListA(var size: Int) : MyList {
        override fun isEmpty(): Boolean = size == 0
    }

    class MyListA1 : MyListA(0) {
        override fun get(idx: Int): Int = throw IllegalStateException("No get")
    }

    class MyListA2 : MyListA(0) {
        private val storage: Array<Int> = emptyArray()
        override fun get(idx: Int): Int = storage[idx]
    }

    abstract class MyListB : MyList

    class MyListB1 : MyListB() {
        private var amount: Int = 0
        override fun get(idx: Int): Int = throw IllegalStateException("No get")
        override fun isEmpty(): Boolean = amount == 0
    }

    class MyListB2 : MyListB() {
        private var size: Int = 0
        private val storage: Array<Int> = emptyArray()
        override fun get(idx: Int): Int = storage[idx]
        override fun isEmpty(): Boolean = size == 0
    }


    private fun MyList.first(): Int {
        if (isEmpty()) throw IllegalArgumentException("Empty")
        return get(0)
    }

    private fun MyList.exceptionIfEmpty(): Int {
        if (isEmpty()) throw IllegalArgumentException("Empty")
        return 0
    }

    fun manyInterfaceImpls1(x: MyList): Int {
        return x.first()
    }

    fun manyInterfaceImpls2(x: MyList): Int {
        return x.exceptionIfEmpty()
    }

}

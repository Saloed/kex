package org.jetbrains.research.kex.smt.z3.fixpoint

data class QueryCheckStatus(
        val stateNotPossible: Boolean = false,
        val positiveNotPossible: Boolean = false,
        val negativeNotPossible: Boolean = false,
        val exclusivenessNotPossible: Boolean = false
) {
    fun raiseIfNotCorrect() {
        if (stateNotPossible || positiveNotPossible || negativeNotPossible || exclusivenessNotPossible)
            throw FixpointQueryException(this)
    }

    class FixpointQueryException(val status: QueryCheckStatus) : Exception() {
        override fun fillInStackTrace(): Throwable = this
    }
}

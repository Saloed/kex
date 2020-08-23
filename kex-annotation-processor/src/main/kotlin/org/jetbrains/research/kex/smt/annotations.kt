package org.jetbrains.research.kex.smt

annotation class SMTDefinitions(
        val solver: String,
        val importPackage: String,
        val context: String,
        val expr: String,
        val sort: String
)

annotation class SMTExpr(val solver: String)

annotation class SMTMemory(val solver: String, val byteSize: Int)

annotation class SMTExprFactory(val solver: String)

annotation class SMTContext(val solver: String)

annotation class SMTConverter(val solver: String)

annotation class AbstractSolver

annotation class Solver(val name: String)
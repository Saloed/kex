package org.jetbrains.research.kex.smt.z3

import org.jetbrains.research.kex.smt.*

@SMTDefinitions(solver = "Z3", importPackage = "com.microsoft.z3", context = "ContextWithIntSortSizeInfo", expr = "Expr", sort = "Sort")
private object Z3

@SMTExpr(solver = "Z3")
abstract class Z3SMTExpr

@SMTMemory(solver = "Z3", byteSize = 32)
abstract class Z3SMTMemory

@SMTExprFactory(solver = "Z3")
abstract class Z3SMTExprFactory

//@SMTContext(solver = "Z3", importPackage = "com.microsoft.z3", context = "ContextWithIntSortSizeInfo")
abstract class Z3SMTContext

@SMTConverter(solver = "Z3")
abstract class Z3SMTConverter
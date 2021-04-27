package org.jetbrains.research.kex.smt.boolector

import org.jetbrains.research.kex.smt.*

@SMTDefinitions(solver = "Boolector", importPackage = "org.jetbrains.research.boolector", context = "Btor", expr = "BoolectorNode", sort = "BoolectorSort")
private object Boolector

@SMTExpr(solver = "Boolector")
abstract class BoolectorSMTExpr

@SMTMemory(solver = "Boolector", byteSize = 32)
abstract class BoolectorSMTMemory

@SMTExprFactory(solver = "Boolector")
abstract class BoolectorSMTExprFactory

@SMTContext(solver = "Boolector")
abstract class BoolectorSMTContext

@SMTConverter(solver = "Boolector")
abstract class BoolectorSMTConverter

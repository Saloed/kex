package org.jetbrains.research.kex.smt.z3.utilities

import com.microsoft.z3.*
import com.microsoft.z3.enumerations.Z3_decl_kind
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import org.jetbrains.research.kex.smt.z3.Z3OptionBuilder
import java.nio.file.Paths
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readText


@OptIn(ExperimentalPathApi::class)
fun main(args: Array<String>) {
    val options = Options()
        .addOption(Option("f", "file", true, "Z3 asserts").apply { isRequired = true })

    val parsedArgs = DefaultParser().parse(options, args)
    val file = parsedArgs.getOptionValue("file").let { Paths.get(it) }
    val smtlib2Source = file.readText()
    val formulaWithBindings = checkFormulasEquality(smtlib2Source)
    println(formulaWithBindings)
}

fun checkFormulasEquality(smtlib2Source: String): String {
    val ctx = Context()
    val asserts = ctx.parseSMTLIB2String(smtlib2Source, emptyArray(), emptyArray(), emptyArray(), emptyArray())
    check(asserts.size >= 2) { "Unexpected asserts" }
    val firstFormula = asserts[0]
    val secondFormula = asserts[1]
    val additionalConstraints = asserts.drop(2)

    val bindings = findVariableBindings(firstFormula, secondFormula, additionalConstraints, ctx)
    println(bindings)

    if (!validateBindings(firstFormula, secondFormula, bindings, ctx)) {
        error("Incorrect bindings")
    }

    return printBindings(firstFormula, secondFormula, bindings, ctx)
}

fun printBindings(first: BoolExpr, second: BoolExpr, bindings: Map<Expr, Expr>, ctx: Context): String {
    val solver = ctx.mkSolver()
    solver.add(first)
    solver.add(second)
    for ((key, value) in bindings.entries.sortedBy { "${it.key}" }) {
        solver.add(ctx.mkEq(key, value))
    }
    return solver.toString()
}

fun validateBindings(
    first: BoolExpr,
    second: BoolExpr,
    bindings: Map<Expr, Expr>,
    ctx: Context
): Boolean {
    val firstVariables = mutableListOf<Expr>()
    val secondVariables = mutableListOf<Expr>()
    val bothVariables = mutableListOf<Expr>()

    for ((firstVar, secondVar) in bindings) {
        check(firstVar.sort == secondVar.sort) { "Sort mismatch" }
        val bothVar = ctx.mkFreshConst("both_var", firstVar.sort)
        firstVariables += firstVar
        secondVariables += secondVar
        bothVariables += bothVar
    }

    val preparedFirst = first.substitute(firstVariables.toTypedArray(), bothVariables.toTypedArray()) as BoolExpr
    val preparedSecond = second.substitute(secondVariables.toTypedArray(), bothVariables.toTypedArray()) as BoolExpr

    validateFormulaHasModel(ctx, preparedFirst, "first formula")
    validateFormulaHasModel(ctx, preparedSecond, "second formula")

    val query = ctx.mkNot(ctx.mkEq(preparedFirst, preparedSecond))
    val solver = ctx.mkSolver()
    solver.add(query)
    solver.checkUnSatOrError("validation")
    return true
}

fun validateFormulaHasModel(ctx: Context, formula: BoolExpr, message: String) {
    val solver = ctx.mkSolver()
    solver.add(formula)
    solver.checkSatOrError("Validation -- no formula: $message")
}

sealed class VariableBindingTree {
    class Node(val expr: Expr, val condition: BoolExpr, val tree: VariableBindingTree) : VariableBindingTree() {
        override fun bindingValue(ctx: Context): Expr = ctx.mkITE(condition, expr, tree.bindingValue(ctx))
        override fun conditions(): List<Expr> = listOf(condition) + tree.conditions()
        override fun eval(model: Model): Expr {
            val conditionValue = model.eval(condition, false)
            return when {
                conditionValue.isTrue -> expr
                conditionValue.isFalse -> tree.eval(model)
                else -> error("Unexpected condition value: $condition = $conditionValue")
            }
        }
    }

    class Leaf(val expr: Expr) : VariableBindingTree() {
        override fun bindingValue(ctx: Context): Expr = expr
        override fun conditions(): List<Expr> = emptyList()
        override fun eval(model: Model): Expr = expr
    }

    abstract fun bindingValue(ctx: Context): Expr
    abstract fun conditions(): List<Expr>
    abstract fun eval(model: Model): Expr

    companion object {
        fun create(ctx: Context, exprs: List<Expr>): VariableBindingTree {
            val result = exprs.fold<Expr, VariableBindingTree?>(null) { tree, expr ->
                when (tree) {
                    null -> Leaf(expr)
                    else -> Node(expr, ctx.mkFreshConst("var_binding", ctx.mkBoolSort()) as BoolExpr, tree)
                }
            }
            return result ?: error("Empty exprs")
        }
    }
}

private fun findVariableBindings(
    first: BoolExpr,
    second: BoolExpr,
    other: List<BoolExpr>,
    ctx: Context
): Map<Expr, Expr> {
    val groups = VariableGroups.group(first, second)
    val arraysRemover = ArraysRemover(ctx)
    val (newFirst, newSecond, newOther) = arraysRemover.removeArrays(first, second, other)
    val arrayVarMapping = arraysRemover.arrayVarsMapping
    val newGroups = groups.map { (f, s) ->
        f.map { arrayVarMapping[it] ?: it } to s.map { arrayVarMapping[it] ?: it }
    }
    val bindings = findVariableBinding(ctx, newFirst, newSecond, newOther, newGroups)
    val arrayReverseMapping = arrayVarMapping.entries.associateBy({ it.value }, { it.key })
    return bindings.map { (f, s) ->
        (arrayReverseMapping[f] ?: f) to (arrayReverseMapping[s] ?: s)
    }.toMap()
}

private fun findVariableBinding(
    ctx: Context,
    first: BoolExpr,
    second: BoolExpr,
    other: List<BoolExpr>,
    groups: List<Pair<List<Expr>, List<Expr>>>
): Map<Expr, Expr> {
    val knownBindings = mutableMapOf<Expr, Expr>()
    val bindingVars = mutableMapOf<Expr, VariableBindingTree>()
    val bindings = mutableListOf<BoolExpr>()

    for ((firstGroup, secondGroup) in groups) {
        check(firstGroup.size == secondGroup.size) { "Group size mismatch" }
        if (firstGroup.size == 1) {
            knownBindings[firstGroup.first()] = secondGroup.first()
            continue
        }
        for (variable in firstGroup) {
            val bindingTree = VariableBindingTree.create(ctx, secondGroup)
            val bindingValue = bindingTree.bindingValue(ctx)
            bindingVars[variable] = bindingTree
            bindings += ctx.mkEq(variable, bindingValue)
        }
    }

    val orderedVariables = (countVariables(first).keys + countVariables(second).keys).toList()
    val allKnowns = ctx.mkAnd(*knownBindings.map { ctx.mkEq(it.key, it.value) }.toTypedArray())
    val allBindings = ctx.mkAnd(*bindings.toTypedArray())

    val solver = ctx.mkSolver()
    val params = ctx.mkParams()
    Z3OptionBuilder()
//        .fp.engine("spacer")
//        .fp.xform.inlineLinear(false)
//        .fp.xform.inlineEager(false)
        .produceUnsatCores(true)
        .addToParams(params)
    solver.setParameters(params)

    solver.add(
        ctx.mkForall(
            ctx.mkImplies(ctx.mkAnd(allKnowns, allBindings), ctx.mkAnd(*other.toTypedArray())),
            orderedVariables
        )
    )
    solver.add(
        ctx.mkForall(
            ctx.mkImplies(ctx.mkAnd(allKnowns, allBindings), ctx.mkEq(first, second)),
            orderedVariables
        )
    )

    solver.checkSatOrError("No binding found")
    val model = solver.model
    val actualBindings = knownBindings.toMutableMap()
    for ((variable, bindingTree) in bindingVars) {
        actualBindings[variable] = bindingTree.eval(model)
    }
    return actualBindings
}

fun Solver.checkSatOrError(message: String) {
    when (check()) {
        Status.SATISFIABLE -> return
        Status.UNSATISFIABLE -> error("UNSATISFIABLE: $message\ncore: ${unsatCore.contentToString()}")
        Status.UNKNOWN -> error("UNKNOWN: $message\nreason: $reasonUnknown")
    }
}

fun Solver.checkUnSatOrError(message: String) {
    when (check()) {
        Status.UNSATISFIABLE -> return
        Status.SATISFIABLE -> error("SATISFIABLE: $message\nmodel: $model")
        Status.UNKNOWN -> error("UNKNOWN: $message\nreason: $reasonUnknown")
    }
}

class VariableGroups private constructor() {
    val variableGroups = mutableListOf<Pair<List<Expr>, List<Expr>>>()

    private fun analyzeVariables(first: Expr, second: Expr) {
        val firstVars = countVariables(first)
        val secondVars = countVariables(second)
        groupByPrefix(firstVars.entries.toList(), secondVars.entries.toList())
    }

    private fun groupByPrefix(first: List<Map.Entry<Expr, Int>>, second: List<Map.Entry<Expr, Int>>) {
        val firstVars = first.groupBy { it.key.variablePrefix() }
        val secondVars = second.groupBy { it.key.variablePrefix() }
        val groups = mergeGroups(firstVars, secondVars) { "Different prefixes" }
        for ((firstGroup, secondGroup) in groups) {
            groupByNumberOfOccurrences(firstGroup, secondGroup)
        }
    }

    private fun groupByNumberOfOccurrences(first: List<Map.Entry<Expr, Int>>, second: List<Map.Entry<Expr, Int>>) {
        val firstVars = first.groupBy({ it.value }, { it.key })
        val secondVars = second.groupBy({ it.value }, { it.key })
        val groups = mergeGroups(firstVars, secondVars) { "Variable count mismatch" }
        for ((firstGroup, secondGroup) in groups) {
            groupByType(firstGroup, secondGroup)
        }
    }

    private fun groupByType(first: List<Expr>, second: List<Expr>) {
        val firstVars = first.groupBy { it.sort }
        val secondVars = second.groupBy { it.sort }
        val groups = mergeGroups(firstVars, secondVars) { "Variable sorts mismatch" }
        for ((firstGroup, secondGroup) in groups) {
            variableGroups += firstGroup to secondGroup
        }
    }

    private inline fun <reified K, V> mergeGroups(
        first: Map<K, List<V>>,
        second: Map<K, List<V>>,
        message: () -> String
    ): List<Pair<List<V>, List<V>>> {
        check(first.keys == second.keys, message)
        val values = mutableListOf<Pair<List<V>, List<V>>>()
        for ((key, firstValue) in first) {
            val secondValue = second.getValue(key)
            check(firstValue.size == secondValue.size) { message() + ": Variable group size mismatch" }
            values += firstValue to secondValue
        }
        return values
    }


    companion object {
        fun group(first: Expr, second: Expr) = VariableGroups()
            .apply { analyzeVariables(first, second) }
            .variableGroups.toList()
    }
}

class ArraysRemover(val ctx: Context) {
    val arrayVarsMapping = mutableMapOf<Expr, Expr>()
    fun removeArrays(
        first: BoolExpr,
        second: BoolExpr,
        other: List<BoolExpr>
    ): Triple<BoolExpr, BoolExpr, List<BoolExpr>> {
        val newFirst = removeArrays(first) as BoolExpr
        val newSecond = removeArrays(second) as BoolExpr
        val newOthers = other.map { removeArrays(it) as BoolExpr }

        return Triple(newFirst, newSecond, newOthers)
    }

    private fun removeArrays(expr: Expr): Expr {
        if (!expr.isApp && !expr.isArray) return expr
        if (expr.isSelect) {
            TODO("SELECT")
        }
        if (expr.isStore) {
            val args = expr.args.map { removeArrays(it) }
            // approximation to find variables mapping
            return args[0]
        }
        if (expr.isArray) {
            val newArrayVar = ctx.mkConst(expr.funcDecl.name, ctx.intSort)
            arrayVarsMapping[expr] = newArrayVar
            return newArrayVar
        }
        if (expr.numArgs == 0) return expr
        val newArgs = expr.args.map { removeArrays(it) }
        val newSorts = newArgs.map { it.sort }.toTypedArray()
        if (newSorts.contentEquals(expr.funcDecl.domain)) {
            return ctx.mkApp(expr.funcDecl, *newArgs.toTypedArray())
        }
        return when (expr.funcDecl.declKind) {
            Z3_decl_kind.Z3_OP_EQ -> ctx.mkEq(newArgs[0], newArgs[1])
            Z3_decl_kind.Z3_OP_AND -> ctx.mkAnd(*newArgs.map { it as BoolExpr }.toTypedArray())
            Z3_decl_kind.Z3_OP_OR -> ctx.mkOr(*newArgs.map { it as BoolExpr }.toTypedArray())
            Z3_decl_kind.Z3_OP_NOT -> ctx.mkNot(newArgs[0] as BoolExpr)
            Z3_decl_kind.Z3_OP_IMPLIES -> ctx.mkImplies(newArgs[0] as BoolExpr, newArgs[1] as BoolExpr)
            Z3_decl_kind.Z3_OP_UNINTERPRETED -> when (expr.name()) {
                "function_call" -> {
                    val newDecl = ctx.mkFuncDecl(expr.funcDecl.name, newSorts, ctx.boolSort)
                    ctx.mkApp(newDecl, *newArgs.toTypedArray())
                }
                else -> TODO("Unexpected uninterpreted function: $expr")
            }
            else -> TODO("Unexpected decl kind: $expr")
        }
    }
}


enum class VarTag(val marker: String) {
    BAD("bad_"), GOOD("good_");
}

private fun Expr.tag(): VarTag {
    val text = name()
    if (text.startsWith(VarTag.BAD.marker)) return VarTag.BAD
    if (text.startsWith(VarTag.GOOD.marker)) return VarTag.GOOD
    error("Unexpected var name: $text")
}

private fun Expr.nameWithoutTag() = name().removePrefix(tag().marker)

private fun String.indexOfOrLast(txt: String) = indexOf(txt).let { if (it != -1) it else lastIndex }

private fun Expr.variablePrefix(): String {
    val name = nameWithoutTag()
    val idx = minOf(name.indexOfOrLast("!"), name.indexOfOrLast("__"), name.indexOfOrLast("#"))
    return name.substring(0, idx)
}

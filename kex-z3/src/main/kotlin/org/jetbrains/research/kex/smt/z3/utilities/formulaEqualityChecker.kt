package org.jetbrains.research.kex.smt.z3.utilities

import org.jetbrains.research.kthelper.collection.firstOrElse
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

    val bindingSearchContext = BindingSearchContext(ctx)
    bindingSearchContext.init(firstFormula, secondFormula, additionalConstraints)
    return bindingSearchContext.loop()
}

sealed class VariableBindingTree {
    class Node(val expr: Expr, val condition: BoolExpr, val tree: VariableBindingTree) : VariableBindingTree() {
        override fun variableSelectCondition(ctx: Context, root: VariableBindingTree): Map<Expr, BoolExpr> =
            tree.variableSelectCondition(ctx, root) + (expr to condition)

        override fun bindingValue(ctx: Context): Expr = ctx.mkITE(ctx.mkAnd(condition), expr, tree.bindingValue(ctx))
        override fun conditions(): List<Expr> = listOf(condition) + tree.conditions()
        override fun eval(model: Model): Expr {
            val conditionValue = model.eval(condition, false)
            return when {
                conditionValue.isTrue -> expr
                conditionValue.isFalse -> tree.eval(model)
                else -> error("Unexpected condition value: $condition = $conditionValue")
            }
        }

        override fun uniqueConstraint(ctx: Context, variablesConditions: Map<Expr, BoolExpr>): BoolExpr {
            val otherSelectors = variablesConditions[expr] ?: ctx.mkFalse()
            val uniquenessConstraint = ctx.mkImplies(condition, ctx.mkNot(otherSelectors))
            val nestedConstraint = tree.uniqueConstraint(ctx, variablesConditions)
            return ctx.mkAnd(uniquenessConstraint, nestedConstraint)
        }

        override fun variables() = listOf(expr) + tree.variables()
        override fun toString() = "$condition -> $expr\n$tree"
    }

    class Leaf(val expr: Expr) : VariableBindingTree() {
        override fun variableSelectCondition(ctx: Context, root: VariableBindingTree): Map<Expr, BoolExpr> {
            val parentConditions = mutableListOf<BoolExpr>()
            var node = root
            while (node is Node) {
                parentConditions += node.condition
                node = node.tree
            }
            val negatedParentConditions = parentConditions.map { ctx.mkNot(it) }
            val condition = ctx.mkAnd(*negatedParentConditions.toTypedArray())
            return mapOf(expr to condition)
        }

        override fun variables() = listOf(expr)
        override fun bindingValue(ctx: Context): Expr = expr
        override fun conditions(): List<Expr> = emptyList()
        override fun eval(model: Model): Expr = expr
        override fun uniqueConstraint(ctx: Context, variablesConditions: Map<Expr, BoolExpr>): BoolExpr = ctx.mkTrue()
        override fun toString() = "else -> $expr"
    }

    fun variableSelectCondition(ctx: Context) = variableSelectCondition(ctx, this)
    protected abstract fun variableSelectCondition(ctx: Context, root: VariableBindingTree): Map<Expr, BoolExpr>
    abstract fun bindingValue(ctx: Context): Expr
    abstract fun conditions(): List<Expr>
    abstract fun variables(): List<Expr>
    abstract fun eval(model: Model): Expr
    abstract fun uniqueConstraint(ctx: Context, variablesConditions: Map<Expr, BoolExpr>): BoolExpr

    companion object {
        fun create(ctx: Context, exprs: List<Expr>, shift: Int): VariableBindingTree {
            val shiftedExprs = ArrayDeque(exprs)
            for (i in 0..shift) {
                shiftedExprs.addLast(shiftedExprs.removeFirst())
            }
            val result = shiftedExprs.fold<Expr, VariableBindingTree?>(null) { tree, expr ->
                when (tree) {
                    null -> Leaf(expr)
                    else -> Node(expr, ctx.mkFreshConst("var_binding", ctx.mkBoolSort()) as BoolExpr, tree)
                }
            }
            return result ?: error("Empty exprs")
        }
    }
}

class BindingSearchContext(val ctx: Context) {
    private lateinit var querySecondFormula: BoolExpr
    private lateinit var queryFirstFormula: BoolExpr
    private lateinit var originalFirst: BoolExpr
    private lateinit var originalSecond: BoolExpr
    private lateinit var arrayReverseMapping: Map<Expr, Expr>
    private lateinit var conditionVariables: Set<Expr>
    private lateinit var queryFormula: BoolExpr
    private lateinit var variableBindingFormula: BoolExpr
    private lateinit var knownBindingFormula: BoolExpr
    private lateinit var orderedVariables: List<Expr>
    private lateinit var bindings: List<BoolExpr>
    private lateinit var uniquenessConstraints: List<BoolExpr>
    private lateinit var knownBindings: MutableMap<Expr, Expr>
    private lateinit var bindingVars: MutableMap<Expr, VariableBindingTree>
    private lateinit var arrayVarMapping: Map<Expr, Expr>
    private val bindingHistory = mutableListOf<Map<Expr, Expr>>()
    private val variableSelectionHistory = mutableListOf<BoolExpr>()
    private val fixedVariableSelectors = mutableListOf<BoolExpr>()

    fun init(first: BoolExpr, second: BoolExpr, other: List<BoolExpr>) {
        originalFirst = first
        originalSecond = second
        val groups = VariableGroups.group(first, second)
        val arraysRemover = ArraysRemover(ctx)
        val (newFirst, newSecond, newOther) = arraysRemover.removeArrays(first, second, other)
        arrayVarMapping = arraysRemover.arrayVarsMapping
        arrayReverseMapping = arrayVarMapping.entries.associateBy({ it.value }, { it.key })
        val newGroups = groups.map { (f, s) ->
            f.map { arrayVarMapping[it] ?: it } to s.map { arrayVarMapping[it] ?: it }
        }
        initFormulas(newFirst, newSecond, newOther, newGroups)
    }

    fun loop(): String {
        while (true) {
            println("-".repeat(50))
            val bindings = searchForBinding()
            println(bindings)
            checkUnboundedVariables(bindings)
            if (validateBindings(bindings, originalFirst, originalSecond)) {
                return printBindings(bindings)
            }
        }
    }

    private fun printBindings(bindings: Map<Expr, Expr>): String {
        val solver = ctx.mkSolver()
        solver.add(originalFirst)
        solver.add(originalSecond)
        for ((firstVar, secondVar) in bindings) {
            solver.add(ctx.mkEq(firstVar, secondVar))
        }
        return solver.toString()
    }


    private fun validateBindings(bindings: Map<Expr, Expr>, firstFormula: BoolExpr, secondFormula: BoolExpr): Boolean {
        val firstVariableList = mutableListOf<Expr>()
        val secondVariableList = mutableListOf<Expr>()
        val bothVariableList = mutableListOf<Expr>()

        for ((firstVar, secondVar) in bindings) {
            check(firstVar.sort == secondVar.sort) { "Variable sort mismatch" }
            val bothVar = ctx.mkFreshConst("both_var", firstVar.sort)
            firstVariableList += firstVar
            secondVariableList += secondVar
            bothVariableList += bothVar
        }

        val firstVariables = firstVariableList.toTypedArray()
        val secondVariables = secondVariableList.toTypedArray()
        val bothVariables = bothVariableList.toTypedArray()

        val preparedFirst = firstFormula.substitute(firstVariables, bothVariables) as BoolExpr
        val preparedSecond = secondFormula.substitute(secondVariables, bothVariables) as BoolExpr

        validateFormulaHasModel(preparedFirst, "first formula")
        validateFormulaHasModel(preparedSecond, "second formula")

        val query = ctx.mkNot(ctx.mkEq(preparedFirst, preparedSecond))
        val solver = ctx.mkSolver()
        solver.add(query)
        return when (solver.check()) {
            Status.UNSATISFIABLE -> true
            Status.UNKNOWN -> error("UNKNOWN: validation\nreason: ${solver.reasonUnknown}")
            Status.SATISFIABLE -> {
                val model = solver.model
                val modelRepresentation = buildString {
                    val constants = model.constDecls.associateWith { model.getConstInterp(it) }
                    for ((bothVar, value) in constants) {
                        val firsVar = ctx.mkConst(bothVar).substitute(bothVariables, firstVariables)
                        val secondVar = ctx.mkConst(bothVar).substitute(bothVariables, secondVariables)
                        appendLine("$firsVar = $secondVar = $value")
                    }
                    val functions = model.funcDecls.associateWith { model.getFuncInterp(it) }
                    for ((decl, interpretation) in functions) {
                        appendLine("$decl = $interpretation")
                    }
                    val firstValue = model.eval(preparedFirst, false)
                    val secondValue = model.eval(preparedSecond, false)
                    appendLine("First: $firstValue")
                    appendLine("Second: $secondValue")
                }
                println("SATISFIABLE: validation\nmodel:\n$modelRepresentation")
                false
            }
        }
    }

    private fun validateFormulaHasModel(formula: BoolExpr, message: String) {
        val solver = ctx.mkSolver()
        solver.add(formula)
        when (solver.check()) {
            Status.SATISFIABLE -> {
            }
            Status.UNSATISFIABLE -> error("UNSATISFIABLE: Validation -- no formula: $message\ncore: ${solver.unsatCore.contentToString()}")
            Status.UNKNOWN -> error("UNKNOWN: Validation -- no formula: $message\nreason: ${solver.reasonUnknown}")
        }
    }

    private fun searchForBinding(): Map<Expr, Expr> {
        val binding = findBinding()
        return unmapArrayVariables(binding)
    }

    private fun initFormulas(
        first: BoolExpr,
        second: BoolExpr,
        other: List<BoolExpr>,
        groups: List<Pair<List<Expr>, List<Expr>>>
    ) {
        initBindings(groups, other, first, second)

        uniquenessConstraints = bindingUniquenessConstraints(bindingVars.values.toList())
        bindings = bindingVars.map { (variable, bindingTree) ->
            val bindingValue = bindingTree.bindingValue(ctx)
            ctx.mkEq(variable, bindingValue)
        }

        orderedVariables = (countVariables(first).keys + countVariables(second).keys).toList()
        knownBindingFormula = ctx.mkAnd(*knownBindings.map { ctx.mkEq(it.key, it.value) }.toTypedArray()).simplifyBool()
        variableBindingFormula = ctx.mkAnd(*bindings.toTypedArray()).simplifyBool()

        val ufRemover = UninterpretedFunctionsRemover(ctx)
        queryFirstFormula = ufRemover.remove(first) as BoolExpr
        querySecondFormula = ufRemover.remove(second) as BoolExpr
        queryFormula = ctx.mkEq(queryFirstFormula, querySecondFormula)

        conditionVariables = bindingVars.values.flatMap { it.conditions() }.toSet()
    }

    private fun initBindings(
        groups: List<Pair<List<Expr>, List<Expr>>>,
        other: List<BoolExpr>,
        first: BoolExpr,
        second: BoolExpr
    ) {
        knownBindings = mutableMapOf()
        bindingVars = mutableMapOf()

        initProvidedBindings(other, first, second)

        val usedFirstVars = knownBindings.keys.toSet()
        val usedSecondVars = knownBindings.values.toSet()
        check(usedFirstVars.size == usedSecondVars.size) { "Duplicates in bindings" }

        for ((firstGroup, secondGroup) in groups) {
            check(firstGroup.size == secondGroup.size) { "Group size mismatch" }
            if (firstGroup.size == 1) {
                val firstVar = firstGroup.first()
                val secondVar = secondGroup.first()
                if (firstVar in knownBindings) {
                    val knownBinding = knownBindings[firstVar]
                    check(secondVar == knownBinding) {
                        "Different bindings found: provided: [$firstVar = $knownBinding]  found: [$firstVar = $secondVar] "
                    }
                    continue
                }
                check(firstVar !in usedFirstVars) { "Try to bind used variable" }
                check(secondVar !in usedSecondVars) { "Try to bind used variable" }
                knownBindings[firstVar] = secondVar
                continue
            }
            val unusedFirstGroup = firstGroup.filter { it !in usedFirstVars }
            val unusedSecondGroup = secondGroup.filter { it !in usedSecondVars }
            check(unusedFirstGroup.size == unusedSecondGroup.size) { "Groups size mismatch" }
            for ((i, variable) in unusedFirstGroup.withIndex()) {
                val bindingTree = VariableBindingTree.create(ctx, unusedSecondGroup, i)
                bindingVars[variable] = bindingTree
            }
        }
    }

    private fun initProvidedBindings(bindings: List<BoolExpr>, first: BoolExpr, second: BoolExpr) {
        val providedBindings = parseProvidedBindings(bindings)
        val firstTag = collectVariables(first).map { it.tag() }.toSet().single()
        val secondTag = collectVariables(second).map { it.tag() }.toSet().single()
        val correctOrderedBindings = providedBindings.map { (f, s) ->
            val newFirst = when (firstTag) {
                f.tag() -> f
                s.tag() -> s
                else -> error("Tags mismatch")
            }
            val newSecond = when (secondTag) {
                f.tag() -> f
                s.tag() -> s
                else -> error("Tags mismatch")
            }
            newFirst to newSecond
        }
        knownBindings.putAll(correctOrderedBindings.toMap())
    }

    private fun parseProvidedBindings(bindings: List<Expr>): List<Pair<Expr, Expr>> = bindings.flatMap {
        when {
            it.isEq -> listOf(it.args[0] to it.args[1])
            it.isAnd -> it.args.flatMap { parseProvidedBindings(it.args.toList()) }
            else -> error("Unexpected provided binding: $it")
        }
    }

    private fun checkUnboundedVariables(bindings: Map<Expr, Expr>) {
        val firstVars = bindings.keys
        val secondVars = bindings.values.toSet()
        check(firstVars.size == secondVars.size) { "Different number of variables" }
        var status = checkUnboundedVariables(firstVars, originalFirst)
        status = status && checkUnboundedVariables(secondVars, originalSecond)
        check(status) { "Incorrect binding" }
    }

    private fun checkUnboundedVariables(usedVariables: Set<Expr>, formula: BoolExpr): Boolean {
        val formulaVariables = collectVariables(formula)
        val unbounded = formulaVariables - usedVariables
        val unknown = usedVariables - formulaVariables
        println("Vars without binding: $unbounded")
        println("Unknown Vars: $unknown")
        return unbounded.isEmpty() && unknown.isEmpty()
    }


    private fun bindingUniquenessConstraints(bindingTrees: List<VariableBindingTree>): List<BoolExpr> {
        val constraints = mutableListOf<BoolExpr>()
        val variableSelects = bindingTrees.map { it.variableSelectCondition(ctx) }
        for ((i, tree) in bindingTrees.withIndex()) {
            val otherTreesSelectors = variableSelects.filterIndexed { idx, _ -> idx != i }
            val otherVariablesConditions = otherTreesSelectors.flatMap { it.entries }
                .groupBy({ it.key }, { it.value })
                .mapValues { (_, conditions) -> ctx.mkOr(*conditions.toTypedArray()) }
            constraints += tree.uniqueConstraint(ctx, otherVariablesConditions)
        }
        val allConstraints = constraints.map { it.simplifyBool() }.toTypedArray()
        return listOf(ctx.mkAnd(*allConstraints).simplifyBool())
    }


    private fun BoolExpr.simplifyBool(): BoolExpr {
        val params = ctx.mkParams()
        params.add("elim_ite", true)
        params.add("ite_extra_rules", true)
        params.add("pull_cheap_ite", true)
        return simplify(params) as BoolExpr
    }

    private fun findBinding(): Map<Expr, Expr> {
        val solver = createSolver()
        addVariableConstrains(solver)
        addQuery(solver)
        println("*".repeat(20))
        println("Call solver")
        val model = querySolver(solver)
        updateBindingHistory(model)
        val bindings = createBindings(model)
        println("Validate query")
        println("*".repeat(20))
        if (!validateBindings(bindings, queryFirstFormula, querySecondFormula)) {
            error("Incorrect search query")
        }
        println("*".repeat(20))
        return bindings
    }

    private fun updateBindingHistory(model: Model) {
        val selectorsValues = conditionVariables.map { ctx.mkEq(it, model.eval(it, false)) }
        variableSelectionHistory += ctx.mkAnd(*selectorsValues.toTypedArray())
    }

    private fun unmapArrayVariables(bindings: Map<Expr, Expr>) = bindings.map { (f, s) ->
        (arrayReverseMapping[f] ?: f) to (arrayReverseMapping[s] ?: s)
    }.toMap()

    private fun createBindings(model: Model): MutableMap<Expr, Expr> {
        val actualBindings = knownBindings.toMutableMap()
        for ((variable, bindingTree) in bindingVars) {
            actualBindings[variable] = bindingTree.eval(model)
        }
        bindingHistory += actualBindings.toMutableMap()
        return actualBindings
    }

    private fun addVariableConstrains(solver: Solver) {
        for (constraint in uniquenessConstraints) {
            solver.add(constraint)
        }
        for (fixedVar in fixedVariableSelectors) {
            solver.add(fixedVar)
        }
        for (checkedVariables in variableSelectionHistory) {
            solver.add(ctx.mkNot(checkedVariables))
        }
    }

    private fun addQuery(solver: Solver) {
        solver.add(
            ctx.mkForall(
                ctx.mkImplies(ctx.mkAnd(knownBindingFormula, variableBindingFormula), queryFormula),
                orderedVariables
            )
        )
    }

    private fun querySolver(solver: Solver): Model {
        when (solver.check()) {
            Status.UNSATISFIABLE -> reportNoBindingFound(solver)
            Status.UNKNOWN -> error("UNKNOWN: No binding found\nreason: ${solver.reasonUnknown}")
            Status.SATISFIABLE -> {
            }
        }
        return solver.model
    }

    private fun reportNoBindingFound(solver: Solver) {
        val bindingSet = bindingHistory.map { it.entries.toMutableSet() }
        for (binding in bindingSet) {
            binding -= knownBindings.entries
        }
        var minedBindings = bindingSet.firstOrElse { emptyList() }.toSet()
        for (binding in bindingSet) {
            minedBindings = minedBindings.intersect(binding)
        }
        val allVarsWithBinding = knownBindings.keys + minedBindings.map { it.key }
        val unboundedVars = bindingVars.filterKeys { it !in allVarsWithBinding }
        val allBoundedVariables = (knownBindings.values + minedBindings.map { it.value }).toSet()

        println("#".repeat(50))
        println("Known bindings")
        for ((f, s) in knownBindings) {
            println("$f = $s")
        }
        println("Mined bindings")
        for ((f, s) in minedBindings) {
            println("$f = $s")
        }
        println("Unknown bindings")
        for ((f, variants) in unboundedVars) {
            println("$f = ${variants.variables().filter { it !in allBoundedVariables }}")
        }
        error("UNSATISFIABLE: No binding found\ncore: ${solver.unsatCore.contentToString()}")
    }

    private fun createSolver(): Solver {
        val solver = ctx.mkSolver()
        val params = ctx.mkParams()
        Z3OptionBuilder()
            //        .fp.engine("spacer")
            //        .fp.xform.inlineLinear(false)
            //        .fp.xform.inlineEager(false)
            .produceUnsatCores(true)
            .addToParams(params)
        solver.setParameters(params)
        return solver
    }
}

private typealias VariableGroup<T> = Pair<List<T>, List<T>>

class VariableGroups private constructor(private val firstFormula: Expr, private val secondFormula: Expr) {

    val variableGroups = mutableListOf<VariableGroup<Expr>>()

    private fun analyzeVariables() {
        val firstVars = countVariables(firstFormula).entries.toList()
        val secondVars = countVariables(secondFormula).entries.toList()
        variableGroups += listOf(firstVars to secondVars)
            .groupWith("Variable prefixes") { vars -> vars.groupBy { it.key.variablePrefix() } }
            .groupWith("Variable count") { vars -> vars.groupBy({ it.value }, { it.key }) }
            .groupWith("Variable sort") { vars -> vars.groupBy { it.sort } }
            .groupByUsagePattern()
            .groupWith("Variable name") { vars -> vars.groupByIfNeeded { it.variableKindByName() } }
    }

    private fun Expr.variableKindByName(): String {
        val untaggedName = nameWithoutTag()
        if (untaggedName.matches(Regex(".*__tr\\d+"))) {
            return "tr_kind"
        }
        if (untaggedName.matches(Regex(".*#level_\\d+!\\d+"))) {
            return "level_kind"
        }
        if (untaggedName.matches(Regex(".*#reach_tag_\\d+_\\d+"))) {
            return "reach_tag_kind"
        }
        return ""
    }

    private inline fun <reified T, reified K> List<T>.groupByIfNeeded(key: (T) -> K): Map<K?, List<T>> {
        if (size <= 1) return mapOf(null to this)
        return groupBy(key)
    }

    private fun List<VariableGroup<Expr>>.groupByUsagePattern() = flatMap { (first, second) ->
        val firstVars = first.groupBy { usagePattern(it, firstFormula) }
        val secondVars = second.groupBy { usagePattern(it, secondFormula) }
        mergeGroups(firstVars, secondVars) { "Variable pattern mismatch" }
    }

    private inline fun <reified T, reified K, reified R> List<VariableGroup<T>>.groupWith(
        name: String,
        grouper: (List<T>) -> Map<K, List<R>>
    ) = flatMap {
        val firstVars = grouper(it.first)
        val secondVars = grouper(it.second)
        mergeGroups(firstVars, secondVars) { "$name mismatch" }
    }

    private inline fun <reified K, V> mergeGroups(
        first: Map<K, List<V>>,
        second: Map<K, List<V>>,
        message: () -> String
    ): List<VariableGroup<V>> {
        check(first.keys == second.keys, message)
        val values = mutableListOf<Pair<List<V>, List<V>>>()
        for ((key, firstValue) in first) {
            val secondValue = second.getValue(key)
            check(firstValue.size == secondValue.size) { message() + ": Variable group size mismatch" }
            values += firstValue to secondValue
        }
        return values
    }

    private fun usagePattern(variable: Expr, formula: Expr): String {
        val usages = UsageCollector.usages(variable, formula).filter { it.isNotEmpty() }
        if (usages.isEmpty()) return "empty"
        val directUsages = usages.map { it.last() }
        val interestingUsages = mutableListOf<String>()
        for (usage in directUsages) {
            when {
                usage.decl.declKind == Z3_decl_kind.Z3_OP_SELECT -> {
                    interestingUsages += "select ${usage.argIdx}"
                }
                usage.decl.declKind == Z3_decl_kind.Z3_OP_STORE -> {
                    interestingUsages += "store ${usage.argIdx}"
                }
                usage.decl.declKind == Z3_decl_kind.Z3_OP_UNINTERPRETED && "${usage.decl.name}" == "function_call" -> {
                    interestingUsages += "fc ${usage.argIdx}"
                }
            }
        }
        return interestingUsages.sorted().joinToString()
    }

    companion object {
        fun group(first: Expr, second: Expr) = VariableGroups(first, second)
            .apply { analyzeVariables() }
            .variableGroups.toList()
    }
}

data class VariableUsage(val decl: FuncDecl, val argIdx: Int)

class UsageCollector private constructor(private val variable: Expr) {
    private val usages = mutableListOf<List<VariableUsage>>()

    private fun visitExpr(expr: Expr, path: List<VariableUsage>) {
        if (expr == variable) {
            usages += path
            return
        }
        if (!expr.isApp) return
        for ((i, arg) in expr.args.withIndex()) {
            val usage = path + VariableUsage(expr.funcDecl, i)
            visitExpr(arg, usage)
        }
    }

    companion object {
        fun usages(variable: Expr, formula: Expr): List<List<VariableUsage>> {
            val collector = UsageCollector(variable)
            collector.visitExpr(formula, emptyList())
            return collector.usages
        }
    }
}

class UninterpretedFunctionsRemover(val ctx: Context) {
    fun remove(expr: Expr): Expr {
        if (!expr.isApp) return expr
        if (expr.isConst) return expr
        val newArgs = expr.args.map { remove(it) }
        if (expr.funcDecl.declKind != Z3_decl_kind.Z3_OP_UNINTERPRETED) {
            return expr.funcDecl.apply(*newArgs.toTypedArray())
        }
        if (expr.funcDecl.name == ctx.mkSymbol("store_approx")) {
            return newArgs[0]
        }
        if (expr.funcDecl.name == ctx.mkSymbol("function_call")) {
            return ctx.mkTrue()
        }
        error("Unexpected UF: $expr")
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

    fun removeArrays(expr: Expr): Expr {
        if (!expr.isApp && !expr.isArray) return expr
        if (expr.isSelect) {
            TODO("SELECT")
        }
        if (expr.isStore) {
            val newArgs = expr.args.map { removeArrays(it) }
            val newSorts = newArgs.map { it.sort }.toTypedArray()
            val newDecl = ctx.mkFuncDecl("store_approx", newSorts, ctx.intSort)
            return ctx.mkApp(newDecl, *newArgs.toTypedArray())
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

private fun String.indexOfOrLast(txt: String) = indexOf(txt).let { if (it != -1) it else length }

private fun Expr.variablePrefix(): String {
    val name = nameWithoutTag()
    val idx = minOf(name.indexOfOrLast("!"), name.indexOfOrLast("__"), name.indexOfOrLast("#"))
    return name.substring(0, idx)
}

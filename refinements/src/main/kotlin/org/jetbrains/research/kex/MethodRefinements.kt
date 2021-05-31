package org.jetbrains.research.kex

import org.jetbrains.research.kthelper.collection.dequeOf
import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.refinements.Refinements
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.refinements.analyzer.method.*
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.visitor.MethodVisitor


class MethodRefinements(
        private val ctx: ExecutionContext,
        private val psa: PredicateStateAnalysis,
        private val debugMethods: List<String> = emptyList()
) : MethodVisitor {

    override val cm: ClassManager
        get() = ctx.cm

    override fun cleanup() {}

    private val excludePackages = hashSetOf<Package>()
    private val excludeClasses = hashSetOf<String>()
    private val excludeMethods = hashSetOf<String>()

    init {
        val letterDigitDollarUnderscore = "[a-zA-Z0-9\$_]"
        val packagePattern = "\\w+(\\.\\w+)*"
        val methodPattern = "$packagePattern\\.$letterDigitDollarUnderscore+::$letterDigitDollarUnderscore+"
        val isPackage = Regex("$packagePattern\\.\\*")
        val isMethod = Regex(methodPattern)
        val isClass = Regex("$packagePattern\\.$letterDigitDollarUnderscore+")
        kexConfig.getMultipleStringValue("refinements", "exclude", ",")
                .forEach {
                    when {
                        it.matches(isMethod) -> excludeMethods.add(it.replace(".", "/"))
                        it.matches(isClass) -> excludeClasses.add(it.replace(".", "/"))
                        it.matches(isPackage) -> excludePackages.add(Package.parse(it))
                        else -> log.error("Unexpected exclude: $it")
                    }
                }
    }

    private val knownRefinements: HashMap<Method, Refinements> = hashMapOf()
    private val methodAnalysisStack = dequeOf<Method>()

    override fun visit(method: Method) {
        super.visit(method)
        if (methodAnalysisStack.isNotEmpty())
            throw IllegalStateException("Method stack must be empty")
        if (debugMethods.isNotEmpty() && method.name !in debugMethods) return
        getOrComputeRefinement(method)
    }

    fun getOrComputeRefinement(method: Method): Refinements {
        if (isExcluded(method)) {
            log.warn("Excluded: $method")
            return Refinements.unknown(method)
        }
        val refinement = knownRefinements[method] ?: analyzeMethod(method)
        knownRefinements[method] = refinement
        return refinement
    }

    fun isExcluded(method: Method) = "${method.klass.fullName}::${method.name}" in excludeMethods || isExcluded(method.klass)
    fun isExcluded(cls: Class) = cls.fullName in excludeClasses || isExcluded(cls.pkg)
    fun isExcluded(pkg: Package) = pkg in excludePackages || excludePackages.any { it.isParent(pkg) }

    private fun analyzeMethod(method: Method): Refinements {
        log.info("Start analysis: $method")
        when {
            method in methodAnalysisStack && method == methodAnalysisStack.last -> {
                knownRefinements[method] = NewRecursiveMethodAnalyzer(cm, psa, this, method).analyzeAndTrackRecursion()
                throw SkipRecursion(method)
            }
            method in methodAnalysisStack -> {
                knownRefinements[method] = Refinements.unknown(method)
                throw SkipRecursion(method)
            }
            else -> {
                methodAnalysisStack.addLast(method)
                val result = analyzerForMethod(method).analyzeAndTrackRecursion()
                methodAnalysisStack.removeLast()
                log.info("Result $method:\n$result")
                return result
            }
        }
    }

    private fun analyzerForMethod(method: Method) = when {
        method.isStatic
                || method.isConstructor
                || method.isFinal -> SimpleMethodAnalyzer(cm, psa, this@MethodRefinements, method)
        else -> OpenMethodAnalyzer(cm, psa, this@MethodRefinements, method)
    }

    private fun MethodAnalyzer.analyzeAndTrackRecursion() = try {
        analyzeSafely()
    } catch (skip: SkipRecursion) {
        if (methodAnalysisStack.isEmpty()) throw IllegalStateException("Empty recursion stack")
        if (methodAnalysisStack.last != skip.method) {
            methodAnalysisStack.removeLast()
            throw skip
        }
        knownRefinements[skip.method] ?: Refinements.unknown(skip.method)
    }

    private fun MethodAnalyzer.analyzeSafely() = try {
        analyze()
    } catch (skip: SkipRecursion) {
        throw skip
    } catch (ex: Exception) {
        log.error("Error in analysis: method $method", ex)
        Refinements.unknown(method)
    } catch (ex: NotImplementedError) {
        log.error("Error in analysis: method $method", ex)
        Refinements.unknown(method)
    }

    private class SkipRecursion(val method: Method) : Exception() {
        override fun fillInStackTrace() = this
    }

}


package org.jetbrains.research.kex.util

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term

open class VariableGenerator(private val prefix: String, private val unique: Boolean = false) {
    private var generatorIndex: Int = 0
    private val indexMapping = hashMapOf<Any, Int>()
    private val objectGeneratorMapping = hashMapOf<Int, VariableGenerator>()
    private val nestedGenerators = hashMapOf<String, VariableGenerator>()
    private var uniqueGenerator: UniqueVariableGenerator? = null
    private var generatedVariable: Term? = null

    fun generatorFor(obj: Any): VariableGenerator {
        val idx = when {
            unique -> generatorIndex++
            else -> indexMapping.getOrPut(obj) { generatorIndex++ }
        }
        return objectGeneratorMapping.getOrPut(idx) { VariableGenerator("${prefix}_${idx}", unique) }
    }

    fun unique(): UniqueVariableGenerator {
        if (unique) return this as UniqueVariableGenerator
        if (uniqueGenerator == null) {
            uniqueGenerator = UniqueVariableGenerator(prefix)
        }
        return uniqueGenerator!!
    }

    fun createNestedGenerator(prefix: String) = nestedGenerators.getOrPut(prefix) { VariableGenerator("${this.prefix}_${prefix}", unique) }
    fun createVar(type: KexType): Term {
        if (generatedVariable == null) {
            generatedVariable = term { value(type, prefix) }
        }
        if (generatedVariable?.type != type) {
            error("Try to generate variable with different type")
        }
        return generatedVariable!!
    }


    private fun allForkedGenerators(): List<VariableGenerator> = objectGeneratorMapping.values + nestedGenerators.values + listOfNotNull(uniqueGenerator)
    fun generatedVariables(): List<Term> = listOfNotNull(generatedVariable) + allForkedGenerators().flatMap { it.generatedVariables() }
}

class UniqueVariableGenerator(prefix: String) : VariableGenerator(prefix, true) {
    fun createUniqueVar(type: KexType) = generatorFor(this).createVar(type)
}

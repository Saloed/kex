package org.jetbrains.research.kex.util

import org.jetbrains.research.kex.ktype.KexType
import org.jetbrains.research.kex.state.term.term

class VariableGenerator(private val prefix: String, private val unique: Boolean = false) {
    private var generatorIndex: Int = 0
    private val indexMapping = hashMapOf<Any, Int>()
    fun generatorFor(obj: Any): VariableGenerator {
        val idx = when {
            unique -> generatorIndex++
            else -> indexMapping.getOrPut(obj) { generatorIndex++ }
        }
        return VariableGenerator("${prefix}_${idx}", unique)
    }

    fun unique() = VariableGenerator(prefix, true)
    fun createVar(type: KexType) = term { value(type, prefix) }
    fun createNestedGenerator(prefix: String) = VariableGenerator("${this.prefix}_${prefix}", unique)
}
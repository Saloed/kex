package org.jetbrains.research.kex.smt.z3.fixpoint

import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import org.jetbrains.research.kex.smt.z3.Z3Context

class DeclarationTracker {
    val declarations = hashSetOf<Declaration>()

    class DeclarationInfo(val name: String, val sort: Sort, val expr: Expr)
    sealed class Declaration(val info: DeclarationInfo? = null) {
        val name: String
            get() = info?.name ?: throw IllegalArgumentException("Declaration without info")
        val expr: Expr
            get() = info?.expr ?: throw IllegalArgumentException("Declaration without info")
        val sort: Sort
            get() = info?.sort ?: throw IllegalArgumentException("Declaration without info")

        class Other(info: DeclarationInfo? = null) : Declaration(info)
        class Argument(val index: Int, info: DeclarationInfo? = null) : Declaration(info)
        class Memory(val memspace: Int, info: DeclarationInfo? = null) : Declaration(info)
        open class Property(val propertyName: String, val memspace: Int, info: DeclarationInfo? = null) : Declaration(info)
        class ClassProperty(val className: String, propertyName: String, memspace: Int, info: DeclarationInfo? = null) : Property(propertyName, memspace, info)

        fun isValuable() = this is Argument || this is Memory || this is Property

        companion object {
            private val argRegexp = Regex("arg\\$(\\d+)")
            private val memoryRegexp = Regex("${Z3Context.MEMORY_NAME}(\\d+)")
            private val classPropertyRegexp = Regex("${Z3Context.PROPERTY_NAME}(\\w+)\\.(\\w+)__(\\d+)")
            private val otherPropertyRegexp = Regex("${Z3Context.PROPERTY_NAME}(\\w+)__(\\d+)")

            fun create(name: String, sort: Sort, expr: Expr): Declaration {
                val matchArgument = argRegexp.find(name)
                val matchMemory = memoryRegexp.find(name)
                val matchClassProperty = classPropertyRegexp.find(name)
                val matchOtherProperty = otherPropertyRegexp.find(name)
                val declarationInfo = DeclarationInfo(name, sort, expr)
                return when {
                    matchArgument != null -> {
                        val idx = matchArgument.groupValues[1].toInt()
                        Argument(idx, declarationInfo)
                    }
                    matchMemory != null -> {
                        val memspace = matchMemory.groupValues[1].toInt()
                        Memory(memspace, declarationInfo)
                    }
                    matchClassProperty != null -> {
                        val groups = matchClassProperty.groupValues
                        val className = groups[1]
                        val propertyName = groups[2]
                        val memspace = groups[3].toInt()
                        ClassProperty(className, propertyName, memspace, declarationInfo)
                    }
                    matchOtherProperty != null -> {
                        val groups = matchOtherProperty.groupValues
                        val propertyName = groups[1]
                        val memspace = groups[2].toInt()
                        Property(propertyName, memspace, declarationInfo)
                    }
                    else -> Other(declarationInfo)
                }
            }
        }
    }

    fun add(name: String, sort: Sort, expr: Expr) {
        declarations.add(Declaration.create(name, sort, expr))
    }

}

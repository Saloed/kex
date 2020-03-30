package org.jetbrains.research.kex.smt.z3.fixpoint

import com.abdullin.kthelper.defaultHashCode
import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import org.jetbrains.research.kex.smt.z3.Z3Context

class DeclarationTracker {
    val declarations = hashSetOf<Declaration>()

    data class DeclarationInfo(val name: String, val sort: Sort, val expr: Expr)
    sealed class Declaration(val info: DeclarationInfo? = null) {
        val name: String
            get() = info?.name ?: throw IllegalArgumentException("Declaration without info")
        val expr: Expr
            get() = info?.expr ?: throw IllegalArgumentException("Declaration without info")
        val sort: Sort
            get() = info?.sort ?: throw IllegalArgumentException("Declaration without info")


        class Other(info: DeclarationInfo? = null) : Declaration(info) {
            override fun toString(): String = "Other(info=$info)"
            override fun hashCode() = info?.hashCode() ?: 0
            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is Other) return false
                return info == other.info
            }
        }

        class This(info: DeclarationInfo? = null) : Declaration(info) {
            override fun toString(): String = "This(info=$info)"
            override fun hashCode() = info?.hashCode() ?: 0
            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is This) return false
                return info == other.info
            }
        }

        class Argument(val index: Int, info: DeclarationInfo? = null) : Declaration(info) {
            override fun toString(): String = "Argument(index=$index info=$info)"
            override fun hashCode() = defaultHashCode(index)
            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is Argument) return false
                return index == other.index
            }
        }

        class Memory(val memspace: Int, info: DeclarationInfo? = null) : Declaration(info) {
            override fun toString(): String = "Memory(memspace=$memspace info=$info)"
            override fun hashCode() = defaultHashCode(memspace)
            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is Memory) return false
                return memspace == other.memspace && info == other.info
            }
        }

        open class Property(val fullName: String, val memspace: Int, info: DeclarationInfo? = null) : Declaration(info) {
            override fun toString(): String = "Property(fullName='$fullName', memspace=$memspace info=$info)"
            override fun hashCode() = defaultHashCode(fullName, memspace)
            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is Property) return false
                return memspace == other.memspace && fullName == other.fullName
            }
        }

        class ClassProperty(val className: String, val propertyName: String, memspace: Int, info: DeclarationInfo? = null) : Property("$className.$propertyName", memspace, info) {
            override fun toString(): String =
                    "ClassProperty(className='$className' propertyName='$propertyName', memspace=$memspace info=$info)"
        }

        class Call(val index: Int, info: DeclarationInfo? = null) : Declaration(info) {
            override fun toString() = "Call(info=$info)"
            override fun hashCode() = info?.hashCode() ?: 0
            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is Call) return false
                return index == other.index
            }
        }

        fun isValuable() = when (this) {
            is This, is Argument, is Memory, is Property, is Call -> true
            else -> false
        }

        companion object {
            private val argRegexp = Regex("arg\\$(\\d+)")
            private val memoryRegexp = Regex("${Z3Context.MEMORY_NAME}(\\d+)")
            private val classPropertyRegexp = Regex("${Z3Context.PROPERTY_NAME}([A-Za-z0-9_/\$]+)\\.(\\w+)__(\\d+)")
            private val otherPropertyRegexp = Regex("${Z3Context.PROPERTY_NAME}(\\w+)__(\\d+)")
            private val callRegexp = Regex("call__(\\d+)")

            fun create(name: String, sort: Sort, expr: Expr): Declaration {
                val matchArgument = argRegexp.find(name)
                val matchMemory = memoryRegexp.find(name)
                val matchClassProperty = classPropertyRegexp.find(name)
                val matchOtherProperty = otherPropertyRegexp.find(name)
                val matchCall = callRegexp.find(name)
                val declarationInfo = DeclarationInfo(name, sort, expr)
                return when {
                    name == "this" -> This(declarationInfo)
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
                    matchCall != null -> {
                        val idx = matchCall.groupValues[1].toInt()
                        Call(idx, declarationInfo)
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

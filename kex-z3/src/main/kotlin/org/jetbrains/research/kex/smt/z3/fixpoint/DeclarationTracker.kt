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

        sealed class Call(val index: Int, info: DeclarationInfo) : Declaration(info) {

            class CallResult(index: Int, info: DeclarationInfo) : Call(index, info) {
                override fun toString(): String = "CallResult(index=$index info=$info)"
                override fun hashCode() = defaultHashCode(index)
                override fun equals(other: Any?): Boolean {
                    if (this === other) return true
                    if (other !is CallResult) return false
                    return index == other.index && info == other.info
                }
            }

            class CallMemory(val memspace: Int, index: Int, info: DeclarationInfo) : Call(index, info) {
                override fun toString(): String = "CallMemory(index=$index memspace=$memspace info=$info)"
                override fun hashCode() = defaultHashCode(memspace)
                override fun equals(other: Any?): Boolean {
                    if (this === other) return true
                    if (other !is CallMemory) return false
                    return memspace == other.memspace && info == other.info && index == other.index
                }
            }

            open class CallProperty(val fullName: String, val memspace: Int, index: Int, info: DeclarationInfo) : Call(index, info) {
                override fun toString(): String = "CallProperty(index = $index fullName='$fullName', memspace=$memspace info=$info)"
                override fun hashCode() = defaultHashCode(fullName, memspace)
                override fun equals(other: Any?): Boolean {
                    if (this === other) return true
                    if (other !is CallProperty) return false
                    return memspace == other.memspace && fullName == other.fullName && info == other.info && index == other.index
                }
            }

            class CallClassProperty(val className: String, val propertyName: String, memspace: Int, index: Int, info: DeclarationInfo) : CallProperty("$className.$propertyName", memspace, index, info) {
                override fun toString(): String =
                        "ClassProperty(index=$index className='$className' propertyName='$propertyName', memspace=$memspace info=$info)"
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
            private val callResultRegexp = Regex("call__(\\d+)__result")
            private val callMemoryRegexp = Regex("call__(\\d+)__${memoryRegexp.pattern}")
            private val callClassProperty = Regex("call__(\\d+)__${classPropertyRegexp.pattern}")
            private val callOtherProperty = Regex("call__(\\d+)__${otherPropertyRegexp.pattern}")

            fun create(name: String, sort: Sort, expr: Expr): Declaration {
                val declarationInfo = DeclarationInfo(name, sort, expr)

                if (name == "this") return This(declarationInfo)

                val matchArgument = argRegexp.find(name)
                if (matchArgument != null) {
                    val idx = matchArgument.groupValues[1].toInt()
                    return Argument(idx, declarationInfo)
                }

                val matchMemory = memoryRegexp.find(name)
                if (matchMemory != null) {
                    val memspace = matchMemory.groupValues[1].toInt()
                    return Memory(memspace, declarationInfo)
                }

                val matchClassProperty = classPropertyRegexp.find(name)
                if (matchClassProperty != null) {
                    val groups = matchClassProperty.groupValues
                    val className = groups[1]
                    val propertyName = groups[2]
                    val memspace = groups[3].toInt()
                    return ClassProperty(className, propertyName, memspace, declarationInfo)
                }

                val matchOtherProperty = otherPropertyRegexp.find(name)
                if (matchOtherProperty != null) {
                    val groups = matchOtherProperty.groupValues
                    val propertyName = groups[1]
                    val memspace = groups[2].toInt()
                    return Property(propertyName, memspace, declarationInfo)
                }

                val matchCallResult = callResultRegexp.find(name)
                if (matchCallResult != null) {
                    val idx = matchCallResult.groupValues[1].toInt()
                    return Call.CallResult(idx, declarationInfo)
                }

                val matchCallMemory = callMemoryRegexp.find(name)
                if (matchCallMemory != null) {
                    val groups = matchCallMemory.groupValues
                    val idx = groups[1].toInt()
                    val memspace = groups[2].toInt()
                    return Call.CallMemory(memspace, idx, declarationInfo)
                }

                val matchCallClassProperty = callClassProperty.find(name)
                if (matchCallClassProperty != null) {
                    val groups = matchCallClassProperty.groupValues
                    val idx = groups[1].toInt()
                    val className = groups[2]
                    val propertyName = groups[3]
                    val memspace = groups[4].toInt()
                    return Call.CallClassProperty(className, propertyName, memspace, idx, declarationInfo)
                }

                val matchCallOtherProperty = callOtherProperty.find(name)
                if (matchCallOtherProperty != null) {
                    val groups = matchCallOtherProperty.groupValues
                    val idx = groups[1].toInt()
                    val propertyName = groups[2]
                    val memspace = groups[3].toInt()
                    return Call.CallProperty(propertyName, memspace, idx, declarationInfo)
                }

                return Other(declarationInfo)
            }
        }
    }

    fun add(name: String, sort: Sort, expr: Expr) {
        declarations.add(Declaration.create(name, sort, expr))
    }

}

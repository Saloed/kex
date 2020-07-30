package org.jetbrains.research.kex.smt.z3.fixpoint

import com.abdullin.kthelper.defaultHashCode
import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import org.jetbrains.research.kex.smt.z3.Z3Context


class DeclarationTracker {
    val declarations = hashSetOf<Declaration>()

    data class DeclarationInfo(val name: String, val sort: Sort, val expr: Expr)
    sealed class Declaration(open val info: DeclarationInfo? = null) {
        val name: String
            get() = info?.name ?: throw IllegalArgumentException("Declaration without info")
        val expr: Expr
            get() = info?.expr ?: throw IllegalArgumentException("Declaration without info")
        val sort: Sort
            get() = info?.sort ?: throw IllegalArgumentException("Declaration without info")


        data class Other(override val info: DeclarationInfo? = null) : Declaration(info)
        data class This(override val info: DeclarationInfo? = null) : Declaration(info)

        data class Argument(val index: Int, override val info: DeclarationInfo? = null) : Declaration(info) {
            override fun hashCode() = defaultHashCode(index)
            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is Argument) return false
                return index == other.index
            }
        }

        interface Memory {
            val memspace: Int
        }

        interface Property {
            val memspace: Int
            val fullName: String
        }

        interface ClassProperty : Property {
            val className: String
            val propertyName: String
        }

        data class NormalMemory(override val memspace: Int, override val info: DeclarationInfo? = null) : Declaration(info), Memory
        open class NormalProperty(override val fullName: String, override val memspace: Int, info: DeclarationInfo? = null) : Declaration(info), Property {
            override fun toString(): String = "Property(fullName='$fullName', memspace=$memspace info=$info)"
            override fun hashCode() = defaultHashCode(fullName, memspace)
            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is NormalProperty) return false
                return memspace == other.memspace && fullName == other.fullName
            }
        }

        data class NormalClassProperty(
                override val className: String,
                override val propertyName: String,
                override val memspace: Int,
                override val info: DeclarationInfo? = null
        ) : NormalProperty("$className.$propertyName", memspace, info), ClassProperty

        sealed class Call(open val index: Int, override val info: DeclarationInfo) : Declaration(info) {
            data class CallResult(override val index: Int, override val info: DeclarationInfo) : Call(index, info)
            data class CallMemory(override val memspace: Int, override val index: Int, override val info: DeclarationInfo) : Call(index, info), Memory
            open class CallProperty(override val fullName: String, override val memspace: Int, index: Int, info: DeclarationInfo) : Call(index, info), Property {
                override fun toString(): String = "CallProperty(index = $index fullName='$fullName', memspace=$memspace info=$info)"
                override fun hashCode() = defaultHashCode(fullName, memspace)
                override fun equals(other: Any?): Boolean {
                    if (this === other) return true
                    if (other !is CallProperty) return false
                    return memspace == other.memspace && fullName == other.fullName && info == other.info && index == other.index
                }
            }

            data class CallClassProperty(
                    override val className: String,
                    override val propertyName: String,
                    override val memspace: Int,
                    override val index: Int,
                    override val info: DeclarationInfo
            ) : CallProperty("$className.$propertyName", memspace, index, info), ClassProperty
        }

        fun isValuable() = when (this) {
            is This, is Argument, is NormalMemory, is NormalProperty, is Call -> true
            else -> false
        }

        fun isMemoryOrCall() = when (this) {
            is NormalMemory, is NormalProperty, is Call -> true
            else -> false
        }

        companion object {
            private val thisRegex = Regex("^this$")
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
                return regexWhen(name) {
                    like(thisRegex) { This(declarationInfo) }
                            ?: like(argRegexp) { (idx) -> Argument(idx.toInt(), declarationInfo) }
                            ?: like(memoryRegexp) { (memspace) -> NormalMemory(memspace.toInt(), declarationInfo) }
                            ?: like(classPropertyRegexp) { (className, propertyName, memspace) -> NormalClassProperty(className, propertyName, memspace.toInt(), declarationInfo) }
                            ?: like(otherPropertyRegexp) { (propertyName, memspace) -> NormalProperty(propertyName, memspace.toInt(), declarationInfo) }
                            ?: like(callResultRegexp) { (idx) -> Call.CallResult(idx.toInt(), declarationInfo) }
                            ?: like(callMemoryRegexp) { (idx, memspace) -> Call.CallMemory(memspace.toInt(), idx.toInt(), declarationInfo) }
                            ?: like(callClassProperty) { (idx, className, propertyName, memspace) -> Call.CallClassProperty(className, propertyName, memspace.toInt(), idx.toInt(), declarationInfo) }
                            ?: like(callOtherProperty) { (idx, propertyName, memspace) -> Call.CallProperty(propertyName, memspace.toInt(), idx.toInt(), declarationInfo) }
                            ?: `else` { Other(declarationInfo) }
                }
            }
        }
    }

    fun add(name: String, sort: Sort, expr: Expr) {
        declarations.add(Declaration.create(name, sort, expr))
    }
}

private inline fun <R> regexWhen(string: String, block: RegexWhen.() -> R): R = RegexWhen(string).block()
private inline class RegexWhen(val regexWhenArg: String) {
    inline fun <R : Any> like(expr: Regex, block: (MatchResult.Destructured) -> R): R? = expr.matchEntire(regexWhenArg)?.destructured?.let(block)
    inline fun <R : Any> `else`(block: () -> R): R = block()
}



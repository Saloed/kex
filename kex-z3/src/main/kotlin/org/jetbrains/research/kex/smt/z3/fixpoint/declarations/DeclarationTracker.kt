package org.jetbrains.research.kex.smt.z3.fixpoint.declarations

import com.abdullin.kthelper.defaultHashCode
import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryVersion

class DeclarationTracker {
    val declarations = hashSetOf<Declaration>()

    data class DeclarationInfo(val name: String, val sort: Sort, val expr: Expr)

    fun add(name: String, sort: Sort, expr: Expr) {
        declarations.add(Declaration.create(name, sort, expr))
    }
}

sealed class Declaration(open val info: DeclarationTracker.DeclarationInfo? = null) {
    val name: String
        get() = info?.name ?: throw IllegalArgumentException("Declaration without info")
    val expr: Expr
        get() = info?.expr ?: throw IllegalArgumentException("Declaration without info")
    val sort: Sort
        get() = info?.sort ?: throw IllegalArgumentException("Declaration without info")

    data class Other(override val info: DeclarationTracker.DeclarationInfo? = null) : Declaration(info)
    data class This(override val info: DeclarationTracker.DeclarationInfo? = null) : Declaration(info) {
        override fun hashCode(): Int = defaultHashCode(javaClass)
        override fun equals(other: Any?): Boolean = this === other || javaClass == other?.javaClass
    }

    data class Argument(val index: Int, override val info: DeclarationTracker.DeclarationInfo? = null) : Declaration(info) {
        override fun hashCode() = defaultHashCode(index, javaClass)
        override fun equals(other: Any?): Boolean = this === other || (javaClass == other?.javaClass && index == (other as Argument).index)
    }

    data class Memory(val descriptor: MemoryDescriptor, val version: MemoryVersion, override val info: DeclarationTracker.DeclarationInfo? = null) : Declaration(info) {
        override fun hashCode(): Int = defaultHashCode(javaClass, descriptor, version)
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false
            other as Memory
            return descriptor == other.descriptor && version == other.version
        }

        fun classPropertyNames() = when (descriptor.memoryType) {
            MemoryType.PROPERTY -> {
                val regex = Regex("([A-Za-z0-9_/\$]+)\\.([A-Za-z0-9_/\$]+)")
                val (className, propertyName) = regex.matchEntire(descriptor.memoryName)?.destructured
                        ?: error("Incorrect class property name: ${descriptor.memoryName}")
                className to propertyName
            }
            else -> error("Only class properties has class name and property name")
        }
    }

    data class CallResult(val index: Int, override val info: DeclarationTracker.DeclarationInfo? = null) : Declaration(info) {
        override fun hashCode() = defaultHashCode(index, javaClass)
        override fun equals(other: Any?): Boolean = this === other || (javaClass == other?.javaClass && index == (other as CallResult).index)
    }

    fun isValuable() = when (this) {
        is This, is Argument, is CallResult, is Memory -> true
        else -> false
    }

    companion object {
        private val thisRegex = Regex("^this\$")
        private val argRegex = Regex("^arg\\$(\\d+)\$")
        private val callResultRegex = Regex("^call__(\\d+)__result\$")
        private val memoryRegex = Regex("^(?<version>${MemoryVersion.machineNameRegex.pattern})__(?<descriptor>${MemoryDescriptor.machineNameRegex.pattern})\$")

        fun create(name: String, sort: Sort, expr: Expr): Declaration {
            val declarationInfo = DeclarationTracker.DeclarationInfo(name, sort, expr)
            return regexWhen(name) {
                like(thisRegex) { This(declarationInfo) }
                        ?: like(argRegex) { (idx) -> Argument(idx.toInt(), declarationInfo) }
                        ?: like(callResultRegex) { (idx) -> CallResult(idx.toInt(), declarationInfo) }
                        ?: likeNamed(memoryRegex) { match ->
                            val descriptor = match["descriptor"]?.value ?: error("No descriptor group")
                            val version = match["version"]?.value ?: error("No version group")
                            Memory(MemoryDescriptor.fromMachineName(descriptor), MemoryVersion.fromMachineName(version), declarationInfo)
                        }
                        ?: `else` { Other(declarationInfo) }
            }
        }
    }
}

private inline fun <R> regexWhen(string: String, block: RegexWhen.() -> R): R = RegexWhen(string).block()
private inline class RegexWhen(val regexWhenArg: String) {
    inline fun <R : Any> like(expr: Regex, block: (MatchResult.Destructured) -> R): R? = expr.matchEntire(regexWhenArg)?.destructured?.let(block)
    inline fun <R : Any> likeNamed(expr: Regex, block: (MatchNamedGroupCollection) -> R): R? = (expr.matchEntire(regexWhenArg)?.groups as? MatchNamedGroupCollection)?.let(block)
    inline fun <R : Any> `else`(block: () -> R): R = block()
}

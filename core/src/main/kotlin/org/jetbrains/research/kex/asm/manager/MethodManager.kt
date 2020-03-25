package org.jetbrains.research.kex.asm.manager

import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.ktype.kexType
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.MethodDesc
import org.jetbrains.research.kfg.ir.value.instruction.ReturnInst

object MethodManager {
    object InlineManager {
        val inliningEnabled = kexConfig.getBooleanValue("inliner", "enabled", true)
        private val ignorePackages = hashSetOf<Package>()
        private val ignoreClasses = hashSetOf<String>()
        private val ignoreMethods = hashSetOf<Method>()

        init {
            val ignores = kexConfig.getMultipleStringValue("inliner", "ignore", ",")
                    .map { it.replace(".", "/") }
            for (name in ignores) {
                when {
                    name.endsWith("*") -> ignorePackages.add(Package(name))
                    else -> ignoreClasses.add(name)
                }
            }
        }

        fun isIgnored(method: Method) = when {
            ignorePackages.any { it.isParent(method.`class`.`package`) } -> true
            ignoreClasses.any { method.cm[it] == method.`class` } -> true
            ignoreMethods.contains(method) -> true
            else -> false
        }

        fun isInlinable(method: Method): Boolean = when {
            !inliningEnabled -> false
            isIgnored(method) -> false
            method.isStatic -> true
            method.isConstructor -> true
            !method.isFinal && !method.`class`.isFinal -> false
            method.flatten().all { it !is ReturnInst } -> false
            else -> true
        }

        fun methodArguments(predicate: CallPredicate): Map<Term, Term> {
            val call = predicate.call as CallTerm
            val calledMethod = call.method
            val mappings = hashMapOf<Term, Term>()
            if (!call.isStatic) {
                val `this` = term { `this`(call.owner.type) }
                mappings[`this`] = call.owner
            }
            if (predicate.hasLhv) {
                val retval = term { `return`(calledMethod) }
                mappings[retval] = predicate.lhv
            }

            for ((index, argType) in calledMethod.argTypes.withIndex()) {
                val argTerm = term { arg(argType.kexType, index) }
                val calledArg = call.arguments[index]
                mappings[argTerm] = calledArg
            }
            return mappings
        }
    }

    object IntrinsicManager {
        private const val intrinsicsClass = "kotlin/jvm/internal/Intrinsics"

        fun checkNotNull(cm: ClassManager) = cm[intrinsicsClass].getMethod(
                "checkParameterIsNotNull",
                MethodDesc(
                        arrayOf(cm.type.objectType, cm.type.stringType),
                        cm.type.voidType
                )
        )

        fun areEqual(cm: ClassManager) = cm[intrinsicsClass].getMethod(
                "areEqual",
                MethodDesc(
                        arrayOf(cm.type.objectType, cm.type.objectType),
                        cm.type.boolType
                )
        )

    }
}

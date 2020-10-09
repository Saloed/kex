package org.jetbrains.research.kex.refinements.analyzer.utils

import org.jetbrains.research.kex.MethodRefinements
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.UnknownInstance
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass

class MethodImplementations(private val cm: ClassManager, private val methodRefinements: MethodRefinements) {
    fun collectImplementations(method: Method): Set<Method> =
            collectInheritors(method.`class`)
                    .mapNotNull { it.getMethodOrNull(method) }
                    .toSet()

    private fun collectInheritors(cls: Class): Set<Class> = when (cls) {
        is OuterClass -> emptySet()
        else -> cm.concreteClasses
                .filter { it.isInheritorOf(cls) }
                .filterNot { methodRefinements.isExcluded(it) }
                .toSet()
    }

    private fun Class.getMethodOrNull(method: Method) = try {
        getMethod(method.name, method.desc)
    } catch (ex: UnknownInstance) {
        null
    }?.let {
        when {
            it.isEmpty() -> null
            else -> it
        }
    }
}

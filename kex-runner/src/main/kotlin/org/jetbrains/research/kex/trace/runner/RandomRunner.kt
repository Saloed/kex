package org.jetbrains.research.kex.trace.runner

import org.jetbrains.research.kthelper.logging.log
import org.jetbrains.research.kex.random.GenerationException
import org.jetbrains.research.kex.random.Randomizer
import org.jetbrains.research.kex.util.isStatic
import java.lang.reflect.Constructor
import java.lang.reflect.Method
import org.jetbrains.research.kfg.ir.Method as KfgMethod

private fun generate(random: Randomizer, klass: Class<*>, method: Method): Pair<Any?, Array<Any?>?> = try {
    val i = when {
        method.isStatic -> null
        else -> random.next(klass)
    }
    val a = method.genericParameterTypes.map { random.next(it) }.toTypedArray()
    i to a
} catch (e: GenerationException) {
    log.debug("Cannot invoke $method")
    log.debug("Cause: ${e.message}")
    null to null
}

private fun generate(random: Randomizer, method: Constructor<*>): Array<Any?>? = try {
   method.genericParameterTypes.map { random.next(it) }.toTypedArray()
} catch (e: GenerationException) {
    log.debug("Cannot invoke $method")
    log.debug("Cause: ${e.message}")
    null
}


open class RandomRunner(method: KfgMethod, loader: ClassLoader, val random: Randomizer)
    : AbstractRunner(method, loader) {

    open fun run(): InvocationResult? {
        val (instance, args) = when {
            method.isConstructor -> null to generate(random, javaConstructor)
            else -> generate(random, javaClass, javaMethod)
        }
        check(args != null) { "Cannot generate parameters to invoke method $method" }

        return try {
            invoke(instance, args)
        } catch (e: TimeoutException) {
            log.error("Failed method $method with timeout, skipping it")
            null
        }
    }
}

abstract class TracingRandomRunner<T>(method: KfgMethod, loader: ClassLoader, val random: Randomizer)
    : TracingAbstractRunner<T>(method, loader) {

    open fun run() : T? {
        val (instance, args) = when {
            method.isConstructor -> null to generate(random, javaConstructor)
            else -> generate(random, javaClass, javaMethod)
        }
        if (args == null || (!method.isStatic && !method.isConstructor && instance == null)) {
            log.error("Cannot generate parameters to invoke method $method")
            return null
        }

        return collectTrace(instance, args)
    }
}
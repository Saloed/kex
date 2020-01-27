package org.jetbrains.research.kex.trace.runner

import org.jetbrains.research.kex.random.Randomizer
import org.jetbrains.research.kex.trace.`object`.Trace
import org.jetbrains.research.kex.trace.`object`.TraceCollectorProxy
import org.jetbrains.research.kfg.ir.Method

class ObjectTracingRunner(method: Method, loader: ClassLoader)
    : TracingAbstractRunner<Trace>(method, loader) {

    lateinit var lastInvocationResult: InvocationResult

    override fun collectTrace(instance: Any?, args: Array<Any?>): Trace {
        val collector = TraceCollectorProxy.enableCollector(method.cm)
        lastInvocationResult = run(instance, args)
        TraceCollectorProxy.disableCollector()
        return Trace(collector.trace)
    }
}

class RandomObjectTracingRunner(method: Method, loader: ClassLoader, random: Randomizer)
    : TracingRandomRunner<Trace>(method, loader, random) {
    override fun collectTrace(instance: Any?, args: Array<Any?>): Trace {
        val collector = TraceCollectorProxy.enableCollector(method.cm)
        run(instance, args)
        TraceCollectorProxy.disableCollector()
        return Trace(collector.trace)
    }
}

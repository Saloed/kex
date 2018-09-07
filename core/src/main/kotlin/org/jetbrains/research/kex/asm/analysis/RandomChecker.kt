package org.jetbrains.research.kex.asm.analysis

import org.jetbrains.research.kex.asm.transform.TraceInstrumenter
import org.jetbrains.research.kex.config.GlobalConfig
import org.jetbrains.research.kex.trace.RandomRunner
import org.jetbrains.research.kex.trace.TraceManager
import org.jetbrains.research.kex.util.log
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.util.JarUtils
import org.jetbrains.research.kfg.visitor.MethodVisitor
import java.io.File
import java.net.URLClassLoader

class RandomChecker(val loader: ClassLoader, val target: File) : MethodVisitor {
    private val runner = GlobalConfig.getBooleanValue("runner", "enabled", false)

    override fun cleanup() {}

    override fun visit(method: Method) {
        super.visit(method)
        if (!runner) return

        val `class` = method.`class`
        val classFileName = "${target.canonicalPath}/${`class`.fullname}.class"
        if (!method.isAbstract && !method.isConstructor) {
            val traceInstructions = TraceInstrumenter(method)
            JarUtils.writeClass(loader, `class`, classFileName)
            val directory = URLClassLoader(arrayOf(target.toURI().toURL()))
            RandomRunner(method, directory).run()
            traceInstructions.forEach { it.parent?.remove(it) }
        }
        JarUtils.writeClass(loader, `class`, classFileName)


        log.info("Results:")
        val tm = TraceManager
        if (!method.isAbstract && !method.isConstructor) {
            when {
                tm.isFullCovered(method) -> log.info("\"$method\" full covered")
                tm.isBodyCovered(method) -> log.info("\"$method\" body covered")
                else -> log.info("\"$method\" is not covered")
            }
        }
    }

}
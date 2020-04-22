package org.jetbrains.research.kex

import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.transform.LoopDeroller
import org.jetbrains.research.kex.config.FileConfig
import org.jetbrains.research.kex.config.RuntimeConfig
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.Jar
import org.jetbrains.research.kfg.KfgConfig
import org.jetbrains.research.kfg.Package
import org.jetbrains.research.kfg.analysis.LoopAnalysis
import org.jetbrains.research.kfg.analysis.LoopSimplifier
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.util.Flags
import java.nio.file.Paths

abstract class KexTest(includeStdlib: Boolean = false, failOnError: Boolean = true) {
    val packageName = "org/jetbrains/research/kex/test"
    val `package` = Package("$packageName/*")
    val jarPath: String
    val cm: ClassManager
    val loader: ClassLoader

    init {
        val rootDir = System.getProperty("root.dir")
        val version = System.getProperty("project.version")
        kexConfig.initialize(RuntimeConfig, FileConfig("$rootDir/kex-test.ini"))
        kexConfig.initLog("$rootDir/kex-test.log")
        RuntimeConfig.setValue("z3", "tacticsFile", "$rootDir/z3.tactics")
        RuntimeConfig.setValue("z3", "paramFile", "$rootDir/z3.params")

        jarPath = "$rootDir/kex-test/target/kex-test-$version-jar-with-dependencies.jar"
        val jar = Jar(jarPath, `package`)
        loader = jar.classLoader
        val jarsToAnalyze = when {
            includeStdlib -> listOf(
                    jar,
                    Jar(Paths.get("$rootDir/lib/rt-mock.jar"), Package.defaultPackage),
                    Jar(jarPath, Package("kotlin/*"))
            )
            else -> listOf(jar)
        }
        cm = ClassManager(KfgConfig(flags = Flags.readAll, failOnError = failOnError))
        cm.initialize(*jarsToAnalyze.toTypedArray())
    }

    protected fun getPSA(method: Method): PredicateStateAnalysis {
        val loops = LoopAnalysis(cm).invoke(method)
        if (loops.isNotEmpty()) {
            LoopSimplifier(cm).visit(method)
            LoopDeroller(cm).visit(method)
        }

        val psa = PredicateStateAnalysis(cm)
        psa.visit(method)
        return psa
    }
}
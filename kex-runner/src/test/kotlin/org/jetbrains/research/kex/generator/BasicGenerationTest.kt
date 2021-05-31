package org.jetbrains.research.kex.generator

import org.jetbrains.research.kex.KexRunnerTest
import org.jetbrains.research.kex.config.RuntimeConfig
import org.jetbrains.research.kex.config.kexConfig
import kotlin.test.AfterTest
import kotlin.test.BeforeTest
import kotlin.test.Test

class BasicGenerationTest : KexRunnerTest() {
    private var oldApiGenerationValue: Boolean = false

    @BeforeTest
    fun initConfig() {
        oldApiGenerationValue = kexConfig.getBooleanValue("recovering", "apiGeneration", false)
        RuntimeConfig.setValue("recovering", "apiGeneration", true)
    }

    @AfterTest
    fun restoreConfig() {
        RuntimeConfig.setValue("recovering", "apiGeneration", oldApiGenerationValue)
    }

    @Test
    fun testBasic() {
        val klass = cm["$packageName/generation/BasicGenerationTests"]
        runPipelineOn(klass)
    }

    @Test
    fun testBasicJava() {
        val klass = cm["$packageName/generation/BasicJavaObjectGeneration"]
        runPipelineOn(klass)
    }

    @Test
    fun testObjectGeneration() {
        val klass = cm["$packageName/generation/ObjectGenerationTests"]
        runPipelineOn(klass)
    }

    @Test
    fun testAbstractClassGeneration() {
        val klass = cm["$packageName/generation/AbstractClassTests"]
        runPipelineOn(klass)
    }
}
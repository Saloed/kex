package org.jetbrains.research.kex

import kotlin.test.Test

class ObjectTest : KexRunnerTest() {

    @Test
    fun testBasicReachability() {
        val klass = cm["$packageName/ObjectTests"]
        testClassReachability(klass)
    }

    @Test
    fun testJavaBasicReachability() {
        val klass = cm["$packageName/ObjectJavaTests"]
        testClassReachability(klass)
    }

}
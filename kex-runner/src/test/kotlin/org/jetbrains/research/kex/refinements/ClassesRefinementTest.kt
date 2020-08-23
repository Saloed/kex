package org.jetbrains.research.kex.refinements

import org.jetbrains.research.kex.ktype.KexClass
import org.jetbrains.research.kex.ktype.KexInt
import org.jetbrains.research.kex.state.ChainState
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.choice
import org.jetbrains.research.kex.state.term.Term
import kotlin.test.Test

class ClassesRefinementTest : RefinementTest("Classes") {

    private val xcls = nestedClass("XCls")

    @Test
    fun testMutablePropertyAndLocalObject() = run("mutablePropertyAndLocalObject") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexClass(xcls), 0).field(KexInt(), "clsFieldA").load() add const(2) equality arg(KexInt(), 1)
                }
            }.withMemoryVersions()
        }
    }

    @Test
    fun testMutablePropertyAndLocalObjectSmall() = run("mutablePropertyAndLocalObjectSmall") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexClass(xcls), 0).field(KexInt(), "clsFieldB").load() add const(2) equality arg(KexInt(), 1)
                }
            }.withMemoryVersions()
        }
    }

    @Test
    fun testMutableProperty() = run("mutableProperty") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexClass(xcls), 0).field(KexInt(), "clsFieldA").load() add const(2) equality arg(KexInt(), 1)
                }
            }.withMemoryVersions()
        }
    }

    @Test
    fun testManyClassArgs() = run("manyClassArgs") {
        refinementFromResource(IllegalArgumentException())
    }

    @Test
    fun testUnusedArgs() = run("unusedArgs") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexClass(xcls), 0).field(KexInt(), "clsFieldB").load() gt const(0) equality const(true)
                }
            }.withMemoryVersions()
        }
    }


    @Test
    fun testComplex() = run("complex") {
        refinement(IllegalArgumentException()) {
            basic {
                path {
                    arg(KexInt(), 2) lt const(0) equality const(true)
                }
            }.withMemoryVersions()
        }

        refinement(IllegalStateException()) {
            val arg0 = term { arg(KexClass(xcls), 0) }
            val arg1 = term { arg(KexClass(xcls), 1) }
            fun Term.fieldA() = term { field(KexInt(), "clsFieldA").load() }
            fun Term.fieldB() = term { field(KexInt(), "clsFieldB").load() }
            ChainState(
                    choice({
                        path {
                            arg0.fieldB() lt arg1.fieldB() equality const(true)
                        }
                    }, {
                        path {
                            (arg0.fieldA() add arg1.fieldA()) lt (const(2) mul arg0.fieldB()) equality const(true)
                        }
                        path {
                            arg0.fieldA() lt arg0.fieldB() equality const(true)
                        }
                    }),
                    choice({
                        path {
                            arg1.fieldB() le arg0.fieldB() equality const(true)
                        }
                    }, {
                        path {
                            (arg0.fieldA() add arg1.fieldA()) lt (arg0.fieldB() add arg1.fieldB()) equality const(true)
                        }
                        path {
                            (arg0.fieldB() add arg1.fieldB()) gt (const(2) mul arg0.fieldA()) equality const(true)
                        }
                    })
            ).withMemoryVersions()
        }
    }
}

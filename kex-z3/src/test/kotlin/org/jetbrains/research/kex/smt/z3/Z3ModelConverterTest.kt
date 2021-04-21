package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.*
import org.jetbrains.research.kex.KexTest
import org.jetbrains.research.kex.ktype.*
import org.jetbrains.research.kex.smt.z3.fixpoint.declarations.ArgumentDeclarations
import org.jetbrains.research.kex.smt.z3.fixpoint.model.FixpointModelConverter
import org.jetbrains.research.kex.smt.z3.fixpoint.model.ModelDeclarationMapping
import org.jetbrains.research.kex.smt.z3.fixpoint.query.recursion.ExternalCallArgMapping
import org.jetbrains.research.kex.smt.z3.fixpoint.query.recursion.ExternalCallDeclarationMapping
import org.jetbrains.research.kex.state.PredicateStateWithPath
import org.jetbrains.research.kex.state.basic
import org.jetbrains.research.kex.state.memory.MemoryAccessScope
import org.jetbrains.research.kex.state.memory.MemoryDescriptor
import org.jetbrains.research.kex.state.memory.MemoryType
import org.jetbrains.research.kex.state.memory.MemoryVersion
import org.jetbrains.research.kex.state.predicate.CallPredicate
import org.jetbrains.research.kex.state.term.CallTerm
import org.jetbrains.research.kex.state.term.IfTerm
import org.jetbrains.research.kex.state.term.Term
import org.jetbrains.research.kex.state.term.term
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.OuterClass
import org.jetbrains.research.kfg.ir.value.instruction.UnreachableInst
import org.jetbrains.research.kfg.type.VoidType
import org.objectweb.asm.tree.ClassNode
import org.objectweb.asm.tree.MethodNode
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class Z3ModelConverterTest : KexTest() {

    @Test
    fun `test int convert`() = TestCase().run {
        val (x, xt) = variable("x", KexInt())
        val (y, yt) = variable("y", KexInt())
        expression {
            mkEq(mkAdd(mkInt(5), x as ArithExpr), y)
        }
        expected {
            val state = basic { state { modelVar(0) equality ((const(5) add xt) eq yt) } }
            val path = basic { path { modelVar(0) equality true } }
            PredicateStateWithPath(state, path)
        }
    }

    @Test
    fun `test bool convert`() = TestCase().run {
        val (x, xt) = variable("x", KexBool())
        val (y, yt) = variable("y", KexBool())
        expression {
            mkEq(mkAnd(x as BoolExpr, y as BoolExpr), mkNot(mkOr(mkNot(x), mkNot(y))))
        }
        expected {
            val state = basic { state { modelVar(0) equality ((xt and yt) eq (xt.not() or yt.not()).not()) } }
            val path = basic { path { modelVar(0) equality true } }
            PredicateStateWithPath(state, path)
        }
    }

    @Test
    fun `test ite convert`() = TestCase().run {
        val (x, xt) = variable("x", KexInt())
        val (y, yt) = variable("y", KexInt())
        val (z, zt) = variable("z", KexInt())
        val (c, ct) = variable("c", KexBool())
        expression {
            mkEq(mkITE(c as BoolExpr, x, y), z)
        }
        expected {
            val state = basic { state { modelVar(0) equality (IfTerm(KexInt(), ct, xt, yt) eq zt) } }
            val path = basic { path { modelVar(0) equality true } }
            PredicateStateWithPath(state, path)
        }
    }

    @Test
    fun `test property read`() = TestCase().run {
        val className = "org/jetbrains/research/kex/test/ObjectTests\$Point"
        val (memory, _) = property(className, "x", KexInt())
        val (owner, ownerT) = variable("o", KexClass(className))
        val (x, xt) = variable("x", KexInt())
        expression {
            mkEq(mkSelect(memory as ArrayExpr, owner), x)
        }
        expected {
            val state = basic {
                state {
                    val fieldValue = ownerT.field(KexInt(), "x", KexClass(className)).load()
                        .withMemoryVersion(MemoryVersion.initial())
                    modelVar(0) equality (fieldValue eq xt)
                }
            }
            val path = basic { path { modelVar(0) equality true } }
            PredicateStateWithPath(state, path)
        }
    }

    @Test
    fun `test property multiclass read`() = TestCase().run {
        val className = "org/jetbrains/research/kex/test/refinements/Inheritance\$MyList"
        val (memory, _) = property(className, "size", KexInt())
        val (owner, ownerT) = variable("o", KexClass(className))
        val (x, xt) = variable("size", KexInt())
        expression {
            mkEq(mkSelect(memory as ArrayExpr, owner), x)
        }
    }

    inner class TestCase {
        private val factory: Z3ExprFactory = Z3ExprFactory()
        private val z3Context: Z3Context = Z3Context.create(factory)
        private val variables = mutableListOf<Pair<Expr, Term>>()
        private val memories = mutableListOf<Pair<Expr, MemoryDescriptor>>()
        private lateinit var expression: Expr
        private lateinit var expectedState: PredicateStateWithPath
        fun variable(name: String, type: KexType): Pair<Expr, Term> {
            val expr = factory.getVarByTypeAndName(type, name).expr
            val term = term { value(type, name) }
            variables += expr to term
            return expr to term
        }

        fun property(klass: String, field: String, type: KexType): Pair<Expr, MemoryDescriptor> {
            val name = "${klass}.${field}"
            val desc = MemoryDescriptor(MemoryType.PROPERTY, name, 0, MemoryAccessScope.RootScope)
            val expr = factory.makeEmptyMemory(name, Z3ExprFactory.getType(type)).inner.expr
            memories += expr to desc
            return expr to desc
        }

        fun expression(builder: Context.() -> Expr) {
            expression = builder(factory.ctx)
        }

        fun modelVar(idx: Int) = term { value(KexBool(), "model_pv_$idx") }

        fun expected(builder: () -> PredicateStateWithPath) {
            expectedState = builder()
        }

        fun run(case: TestCase.() -> Unit) {
            case()
            val declMapping = declarationMapping()
            val converter = FixpointModelConverter(declMapping, cm.type, z3Context)

            val actual = converter.apply(expression)
            println(actual)
            assertTrue(::expectedState.isInitialized, "Expected state is not provided")
            assertEquals(expectedState, actual.state)
        }

        private fun declarationMapping(): ExternalCallDeclarationMapping {
            val mapping = ExternalCallArgMapping(
                term { value(KexVoid(), "_____dummy_____") },
                factory.ctx.mkFreshConst("dummy", factory.ctx.boolSort),
                variables.map { it.second to it.first },
                memories.map { it.second to it.first },
                term { value(KexVoid(), "_____dummy_____") },
                factory.ctx.mkFreshConst("dummy", factory.ctx.boolSort),
                emptyList()
            )
            val emptyArgs = ArgumentDeclarations.create(emptyList())
            val declarations = ModelDeclarationMapping(emptyArgs)

            val dummyCallTerm = CallTerm(
                KexVoid(),
                term { value(KexVoid(), "dummy") },
                Method(
                    cm,
                    MethodNode().apply {
                        name = "dummy"
                        desc = "V;"
                    },
                    OuterClass(cm, ClassNode().apply { name = "dummy" })
                ),
                UnreachableInst(0, VoidType),
                emptyList()
            )
            val dummyCall = CallPredicate(null, dummyCallTerm)

            return ExternalCallDeclarationMapping(declarations, mapping, 0, dummyCall)
        }

    }


}

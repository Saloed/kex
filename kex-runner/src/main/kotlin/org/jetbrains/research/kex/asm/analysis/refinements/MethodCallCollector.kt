package org.jetbrains.research.kex.asm.analysis.refinements

import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.visitor.MethodVisitor

class MethodCallCollector(override val cm: ClassManager) : MethodVisitor {
    override fun cleanup() {}

    val calls = mutableSetOf<CallInst>()

    override fun visitCallInst(inst: CallInst) {
        super.visitCallInst(inst)
        calls.add(inst)
    }

    companion object {
        fun calls(cm: ClassManager, method: Method): List<CallInst> {
            val collector = MethodCallCollector(cm)
            collector.visit(method)
            return collector.calls.toList()
        }
    }
}

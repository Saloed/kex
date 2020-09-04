package org.jetbrains.research.kex.asm.analysis.refinements.analyzer

import org.jetbrains.research.kex.asm.manager.MethodManager
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.CallInst
import org.jetbrains.research.kfg.visitor.MethodVisitor

class MethodCallCollector(override val cm: ClassManager) : MethodVisitor {
    override fun cleanup() {}
    private val im = MethodManager.IntrinsicManager
    val calls = mutableSetOf<CallInst>()

    override fun visitCallInst(inst: CallInst) {
        super.visitCallInst(inst)
        when (inst.method) {
            im.checkNotNull(cm) -> return
            im.areEqual(cm) -> return
            else -> calls.add(inst)
        }
    }

    companion object {
        fun calls(cm: ClassManager, method: Method): List<CallInst> {
            val collector = MethodCallCollector(cm)
            collector.visit(method)
            return collector.calls.toList()
        }
    }
}

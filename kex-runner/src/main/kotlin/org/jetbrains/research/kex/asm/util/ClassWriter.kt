package org.jetbrains.research.kex.asm.util

import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.util.write
import org.jetbrains.research.kfg.visitor.ClassVisitor
import java.nio.file.Path
import java.nio.file.Paths

class ClassWriter(val ctx: ExecutionContext, val target: Path) : ClassVisitor {
    override val cm: ClassManager
        get() = ctx.cm

    override fun cleanup() {}

    override fun visit(klass: Class) {
        val classFilePath = Paths.get("$target", "${klass.fullName}.class")
        val classFileName = "${classFilePath.toAbsolutePath()}"
        klass.write(cm, ctx.loader, classFileName)
    }
}

package org.jetbrains.research.kex.asm.analysis

import com.abdullin.kthelper.algorithm.DominatorTreeBuilder
import com.abdullin.kthelper.logging.debug
import com.abdullin.kthelper.logging.log
import kotlinx.serialization.Contextual
import kotlinx.serialization.Serializable
import org.jetbrains.research.kex.ExecutionContext
import org.jetbrains.research.kex.asm.manager.isImpactable
import org.jetbrains.research.kex.asm.state.PredicateStateAnalysis
import org.jetbrains.research.kex.asm.transform.originalBlock
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.generator.Generator
import org.jetbrains.research.kex.random.GenerationException
import org.jetbrains.research.kex.random.Randomizer
import org.jetbrains.research.kex.serialization.KexSerializer
import org.jetbrains.research.kex.smt.Checker
import org.jetbrains.research.kex.smt.ReanimatedModel
import org.jetbrains.research.kex.smt.Result
import org.jetbrains.research.kex.state.PredicateState
import org.jetbrains.research.kex.trace.TraceManager
import org.jetbrains.research.kex.trace.`object`.Trace
import org.jetbrains.research.kex.trace.runner.ObjectTracingRunner
import org.jetbrains.research.kex.trace.runner.TimeoutException
import org.jetbrains.research.kfg.ClassManager
import org.jetbrains.research.kfg.ir.BasicBlock
import org.jetbrains.research.kfg.ir.Class
import org.jetbrains.research.kfg.ir.Method
import org.jetbrains.research.kfg.ir.value.instruction.UnreachableInst
import org.jetbrains.research.kfg.visitor.MethodVisitor
import java.nio.file.Files
import java.nio.file.Paths

private val failDir get() = kexConfig.getStringValue("debug", "dump-directory", "./fail")

class KexCheckerException(val inner: Exception, val reason: PredicateState) : Exception()
class KexRunnerException(val inner: Exception, val model: ReanimatedModel) : Exception()

@Serializable
data class Failure(
        @Contextual val `class`: Class,
        @Contextual val method: Method,
        val message: String,
        val state: PredicateState
)

class MethodChecker(
        val ctx: ExecutionContext,
        private val tm: TraceManager<Trace>,
        private val psa: PredicateStateAnalysis) : MethodVisitor {
    override val cm: ClassManager get() = ctx.cm
    val random: Randomizer get() = ctx.random
    val loader: ClassLoader get() = ctx.loader
    val generator = Generator(ctx, psa)

    private fun dumpPS(method: Method, message: String, state: PredicateState) {
        val failDirPath = Paths.get(failDir)
        if (!Files.exists(failDirPath)) {
            Files.createDirectory(failDirPath)
        }
        val errorDump = Files.createTempFile(failDirPath, "ps-", ".json").toFile()
        log.error("Failing saved to file ${errorDump.path}")
        errorDump.writeText(KexSerializer(cm).toJson(Failure(method.`class`, method, message, state)))
    }

    override fun cleanup() {}

    override fun visit(method: Method) {
        super.visit(method)

        if (method.`class`.isSynthetic) return
        if (method.isAbstract || method.isStaticInitializer) return
        if (!method.isImpactable) return

        log.debug("Checking method $method")
        log.debug(method.print())
        log.debug()

        val unreachableBlocks = mutableSetOf<BasicBlock>()
        val domTree = DominatorTreeBuilder(method).build()
        val order: SearchStrategy = DfsStrategy(method)

        for (block in order) {
            if (block.terminator is UnreachableInst) {
                unreachableBlocks += block
                continue
            }

            val originalBlock = block.originalBlock
            if (tm.isCovered(method, originalBlock)) continue

            if (block in unreachableBlocks) continue
            if (domTree[block]?.idom?.value in unreachableBlocks) {
                unreachableBlocks += block
                continue
            }

            val coverageResult = try {
                log.debug("Checking reachability of ${block.name}")
                coverBlock(method, block)
            } catch (e: TimeoutException) {
                log.warn("Timeout exception when running method $method, skipping it")
                break
            } catch (e: KexCheckerException) {
                log.error("Fail when covering block ${block.name} of $method")
                log.error("Error: ${e.inner}")
                dumpPS(method, e.inner.toString(), e.reason)
                break
            } catch (e: KexRunnerException) {
                log.error("Fail when running method $method with model ${e.model}")
                log.error("Error: ${e.inner}")
                break
            }

            log.debug("Block ${block.name} is covered = ${tm.isCovered(method, originalBlock)}")
            log.debug()

            if (coverageResult is Result.UnsatResult) unreachableBlocks += block
        }
        cleanup()
    }

    private fun coverBlock(method: Method, block: BasicBlock): Result {
        val checker = Checker(method, loader, psa)
        val ps = checker.createState(block.terminator)
                ?: return Result.UnknownResult("Could not create a predicate state for instruction")

        val result = try {
            checker.prepareAndCheck(ps)
        } catch (e: Exception) {
            throw KexCheckerException(e, ps)
        }
        when (result) {
            is Result.SatResult -> {
                val (instance, args) = try {
                    generator.generate(method, block, checker.state, result.model)
                } catch (e: GenerationException) {
                    log.warn(e.message)
                    return result
                }

                try {
                    collectTrace(method, instance, args)
                } catch (e: TimeoutException) {
                    throw e
                } catch (e: Exception) {
                    throw KexRunnerException(e, ReanimatedModel(method, instance, args.toList()))
                }
            }
            is Result.UnsatResult -> log.debug("Instruction ${block.terminator.print()} is unreachable")
            is Result.UnknownResult -> log.debug("Can't decide on reachability of " +
                    "instruction ${block.terminator.print()}, reason: ${result.reason}")
        }
        return result
    }

    private fun collectTrace(method: Method, instance: Any?, args: Array<Any?>) {
        val runner = ObjectTracingRunner(method, loader)
        val trace = runner.collectTrace(instance, args)
        tm[method] = trace
    }
}

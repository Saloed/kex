package org.jetbrains.research.kex.asm.analysis.refinements.solver

import com.abdullin.kthelper.logging.log
import kotlinx.serialization.ImplicitReflectionSerializer
import org.jetbrains.research.kex.config.kexConfig
import org.jetbrains.research.kex.serialization.KexSerializer
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import org.jetbrains.research.kex.smt.z3.fixpoint.QueryCheckStatus
import org.jetbrains.research.kex.smt.z3.fixpoint.RecoveredModel
import org.jetbrains.research.kfg.ClassManager
import java.nio.file.Files
import java.nio.file.Paths

val failDir: String
    get() = kexConfig.getStringValue("debug", "dump-directory", "fail")

class FixpointSolver(val cm: ClassManager) {
    inline fun query(crossinline query: Z3FixpointSolver.() -> FixpointResult): List<RecoveredModel> =
            query(query, { result -> result }, { ex -> throw IllegalStateException("Solver error: $ex") })

    inline fun query(crossinline query: Z3FixpointSolver.() -> FixpointResult, crossinline onError: FixpointSolver.(FixpointResult?) -> List<RecoveredModel>): List<RecoveredModel> =
            query(query, { result -> result }, onError)

    inline fun querySingle(crossinline query: Z3FixpointSolver.() -> FixpointResult): RecoveredModel =
            query(query, { result -> result.first() }, { ex -> throw IllegalStateException("Solver error: $ex") })

    inline fun querySingle(crossinline query: Z3FixpointSolver.() -> FixpointResult, crossinline onError: FixpointSolver.(FixpointResult?) -> RecoveredModel): RecoveredModel =
            query(query, { result -> result.first() }, onError)

    inline fun <reified T> query(
            crossinline query: Z3FixpointSolver.() -> FixpointResult,
            crossinline onResult: FixpointSolver.(List<RecoveredModel>) -> T,
            crossinline onError: FixpointSolver.(FixpointResult?) -> T
    ): T = try {
        when (val result = Z3FixpointSolver(cm.type).query()) {
            is FixpointResult.Sat -> onResult(result.result)
            is FixpointResult.Unknown -> {
                log.error("Unknown: ${result.reason}")
                onError(result)
            }
            is FixpointResult.Unsat -> {
                log.error("Unsat: ${result.core.contentToString()}")
                onError(result)
            }
        }
    } catch (ex: QueryCheckStatus.FixpointQueryException) {
        log.error("Bad fixpoint query: ${ex.status}")
        onError(null)
    }

    @OptIn(ImplicitReflectionSerializer::class)
    inline fun <reified T : Any> dumpSolverArguments(args: T) {
        val failDirPath = Paths.get(failDir)
        if (!Files.exists(failDirPath)) {
            Files.createDirectory(failDirPath)
        }
        val serialized = KexSerializer(cm).toJson(args)
        val errorDump = Files.createTempFile(failDirPath, "ps-", ".json").toFile()
        log.error("Arguments saved to file ${errorDump.path}")
        errorDump.writeText(serialized)
        Paths.get(failDir, "last-fail.json").toFile().writeText(serialized)
    }
}
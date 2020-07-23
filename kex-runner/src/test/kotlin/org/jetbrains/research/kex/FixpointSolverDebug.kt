package org.jetbrains.research.kex

import kotlinx.serialization.ImplicitReflectionSerializer
import org.jetbrains.research.kex.asm.analysis.refinements.CallResolver
import org.jetbrains.research.kex.asm.analysis.refinements.solver.CallResolvingRefinementSourcesAnalyzer
import org.jetbrains.research.kex.serialization.KexSerializer
import org.jetbrains.research.kex.smt.z3.Z3FixpointSolver
import org.jetbrains.research.kex.smt.z3.fixpoint.FixpointResult
import java.nio.file.Paths
import kotlin.test.Test

class FixpointSolverDebug : KexTest() {
    @OptIn(ImplicitReflectionSerializer::class)
    inline fun <reified T : Any> run(name: String, execute: (T) -> Unit) {
        val file = Paths.get("fails", name).toFile()
        val data = KexSerializer(cm).fromJson<T>(file.readText())
        execute(data)
    }

    @Test
    fun debugCallResolver() = run("last-fail.json") { args: CallResolver.SolverArgument ->
        val res = Z3FixpointSolver(cm.type).refineWithFixpointSolver(args.positive, args.negative, args.arguments)
        assert(res is FixpointResult.Sat) { res }
        println((res as FixpointResult.Sat).result)
    }

    @Test
    fun debugAnalyzer() = run("last-fail.json") { args: CallResolvingRefinementSourcesAnalyzer.SolverQueryArgument ->
        val res = Z3FixpointSolver(cm.type).mkFixpointQueryV2(args.state, args.sources, args.normals)
        assert(res is FixpointResult.Sat) { res }
        println((res as FixpointResult.Sat).result)
    }
}
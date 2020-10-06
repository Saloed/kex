package org.jetbrains.research.kex

import com.abdullin.kthelper.logging.debug
import com.abdullin.kthelper.logging.log
import org.jetbrains.research.kex.refinements.solver.FixpointSolver
import org.jetbrains.research.kex.refinements.solver.SolverQuery
import org.jetbrains.research.kex.serialization.RefinementsKexSerializer
import java.nio.file.Paths
import kotlin.test.Test

class FixpointSolverDebug : KexTest() {
    private fun run(name: String, execute: (SolverQuery<*, *>) -> Unit) {
        val file = Paths.get("fails", name).toFile()
        val query = RefinementsKexSerializer(cm).fromJson(file.readText(), SolverQuery::class)
        execute(query)
    }

    private fun checkSat(query: SolverQuery<*, *>) {
        log.debug(query)
        val solver = FixpointSolver(cm)
        val res = query.run(solver)
        assert(false) { "$res" }
    }

    @Test
    fun lastFail() = run("last-fail.json", ::checkSat)

    @Test
    fun query() {
        val postfix = System.getProperty("querypostfix") ?: error("No query postfix in environment")
        run("query-${postfix}.json", ::checkSat)
    }
}

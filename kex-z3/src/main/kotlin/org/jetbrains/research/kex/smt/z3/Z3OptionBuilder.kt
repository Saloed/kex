package org.jetbrains.research.kex.smt.z3

import com.microsoft.z3.Params

open class Z3Option(val name: String, val value: String) {
    fun toSmtLib() = "(set-option :$name $value)"
    open fun addToParams(params: Params) = params.apply { add(name, value) }
}

class Z3BooleanOption(name: String, private val boolValue: Boolean) : Z3Option(name, "$boolValue") {
    override fun addToParams(params: Params) = params.apply { add(name, boolValue) }
}

class Z3IntOption(name: String, private val intValue: Int) : Z3Option(name, "$intValue") {
    override fun addToParams(params: Params) = params.apply { add(name, intValue) }
}

class Z3OptionBuilder(val params: List<Z3Option> = emptyList()) {
    val fp = Z3FpOptions(this, "fp")

    fun smtLib() = params.joinToString("\n") { it.toSmtLib() }
    fun addToParams(z3Params: Params) = params.fold(z3Params) { acc, z3Option -> z3Option.addToParams(acc) }


    fun add(name: String, value: Boolean) = Z3OptionBuilder(params + Z3BooleanOption(name, value))
    fun add(name: String, value: Int) = Z3OptionBuilder(params + Z3IntOption(name, value))
    fun add(name: String, value: String) = Z3OptionBuilder(params + Z3Option(name, value))


    fun produceUnsatCores(value: Boolean) = this.add("unsat_core", value)
    fun timeout(value: Int) = this.add("timeout", value)

    class Z3FpOptions(val builder: Z3OptionBuilder, val prefix: String) {
        val xform = Z3FpXformOptions(builder, "$prefix.xform")
        val spacer = Z3FpSpacerOptions(builder, "$prefix.spacer")
        val datalog = Z3FpDatalogOptions(builder, "$prefix.datalog")

        fun engine(name: String) = builder.add("$prefix.engine", name)
        fun generateProofTrace(value: Boolean) = builder.add("$prefix.generate_proof_trace", value)

        class Z3FpXformOptions(val builder: Z3OptionBuilder, val prefix: String) {
            fun inlineEager(value: Boolean) = builder.add("$prefix.inline_eager", value)
            fun inlineLinear(value: Boolean) = builder.add("$prefix.inline_linear", value)
            fun compressUnbound(value: Boolean) = builder.add("$prefix.compress_unbound", value)
        }

        class Z3FpSpacerOptions(val builder: Z3OptionBuilder, val prefix: String) {
            val iuc = Z3FpSpacerIucOptions(builder, "$prefix.iuc")

            class Z3FpSpacerIucOptions(val builder: Z3OptionBuilder, val prefix: String) {
                fun debugProof(value: Boolean) = builder.add("$prefix.debug_proof", value)
            }

            fun q3(value: Boolean) = builder.add("$prefix.q3", value)
            fun simplifyPob(value: Boolean) = builder.add("$prefix.simplify_pob", value)
        }

        class Z3FpDatalogOptions(val builder: Z3OptionBuilder, val prefix: String) {
            fun generateExplanations(value: Boolean) = builder.add("$prefix.generate_explanations", value)
            fun similarityCompressor(value: Boolean) = builder.add("$prefix.similarity_compressor", value)
            fun unboundCompressor(value: Boolean) = builder.add("$prefix.unbound_compressor", value)
            fun subsumption(value: Boolean) = builder.add("$prefix.subsumption", value)
        }

    }

}

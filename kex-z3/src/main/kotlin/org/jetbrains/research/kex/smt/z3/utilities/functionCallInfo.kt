package org.jetbrains.research.kex.smt.z3.utilities

import com.charleskorn.kaml.EmptyYamlDocumentException
import com.charleskorn.kaml.Yaml
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.decodeFromString
import java.nio.file.Path
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readText

@Serializable
data class FunctionCallArg(val name: String, val type: String)

@Serializable
data class FunctionCallInfo(
    val idx: Int,
    @SerialName("in_args")
    val inArgs: List<FunctionCallArg>,
    @SerialName("out_args")
    val outArgs: List<FunctionCallArg>,
    val definition: String
) {
    val idxArg = FunctionCallArg("call_id", "Int")

    val args by lazy { inArgs + outArgs }
    val allArgsWithIndex by lazy { listOf(idxArg) + args }

    fun smtlibDefineStatement(): String =
        "(define-fun function_call (${allArgsWithIndex.joinToString(" ") { "(${it.name} ${it.type})" }}) Bool $definition)"

    fun smtlibDeclareStatement(): String =
        "(declare-fun function_call (${allArgsWithIndex.joinToString(" ") { it.type }}) Bool)"

    fun smtlibFunctionDefinition() = """
        ${smtlibDeclareStatement()}
        ${allArgsWithIndex.joinToString ("\n"){ "(declare-fun ${it.name} () ${it.type})" }}
        (assert 
        (=> (= ${idxArg.name} ${idx})
            (= 
                (function_call  ${allArgsWithIndex.joinToString(" ") { it.name }} )
                $definition
            )
        )
        )
    """.trimIndent()

    fun smtlibParseableDefAsAssert() = """
        (assert $definition)
    """.trimIndent()


    companion object {
        @OptIn(ExperimentalPathApi::class)
        fun load(file: Path): List<FunctionCallInfo> {
            val fileContent = file.readText()
            return try {
                Yaml.default.decodeFromString(fileContent)
            } catch (ex: EmptyYamlDocumentException) {
                emptyList()
            }
        }
    }
}

package org.jetbrains.research.kex.smt.z3.utilities

import com.charleskorn.kaml.EmptyYamlDocumentException
import com.charleskorn.kaml.Yaml
import kotlinx.serialization.Serializable
import kotlinx.serialization.decodeFromString
import java.nio.file.Path
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.readText

@Serializable
data class FunctionCallArg(val name: String, val type: String)

@Serializable
data class FunctionCallInfo(val idx: Int, val args: List<FunctionCallArg>, val definition: String) {
    fun smtlibDefineStatement(): String =
        "(define-fun function_call ((call_id Int) ${args.joinToString(" ") { "(${it.name} ${it.type})" }}) Bool $definition)"

    fun smtlibDeclareStatement(): String =
        "(declare-fun function_call ( Int ${args.joinToString(" ") { it.type }}) Bool)"


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

import org.gradle.api.artifacts.ProjectDependency
import org.gradle.api.artifacts.dsl.DependencyHandler
import org.gradle.api.plugins.ExtensionAware
import org.gradle.api.tasks.SourceSetContainer
import org.gradle.api.tasks.SourceSetOutput
import org.gradle.kotlin.dsl.get

fun String?.versionModifier() = when {
    this == null -> ""
    else -> ":$this"
}

fun DependencyHandler.kfg() = "org.jetbrains.research:kfg:${`kfg-version`}"

fun DependencyHandler.kotlinx(module: String, version: String? = null): String =
    "org.jetbrains.kotlinx:kotlinx-${module}${version.versionModifier()}"

fun ProjectDependency.tests(): SourceSetOutput {
    val sourceSets = (dependencyProject as ExtensionAware).extensions.getByName("sourceSets") as SourceSetContainer
    return sourceSets["test"].output
}

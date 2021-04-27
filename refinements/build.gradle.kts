import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.research.kex-base")
    kotlin("plugin.serialization") version `kotlin-version`
}

dependencies {
    implementation(project(":core"))
    implementation(project(":kex-z3"))
    implementation(project(":kex-runner"))
    implementation("org.jetbrains.research:kfg:${`kfg-version`}")
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json-jvm:${`serialization-version`}")
    implementation("ru.spbstu:ktuples:0.0.1.11")
    testImplementation(project(":core").dependencyProject.sourceSets["test"].output)
    testRuntimeOnly(project(":kex-test"))
}

description = "refinements"


tasks {
    withType<KotlinCompile> {
        kotlinOptions.freeCompilerArgs += "-Xopt-in=kotlin.RequiresOptIn"
    }
}

import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.research.kex-base")
    kotlin("plugin.serialization") version `kotlin-version`
}

dependencies {
    implementation(project(":core"))
    implementation(project(":kex-z3"))
    implementation(project(":kex-runner"))
    implementation(kfg())
    implementation(kotlinx("serialization-json-jvm", `serialization-version`))
    testImplementation(project(":core").tests())
    testRuntimeOnly(project(":kex-test"))
}

description = "refinements"


tasks {
    withType<KotlinCompile> {
        kotlinOptions.freeCompilerArgs += "-Xopt-in=kotlin.RequiresOptIn"
    }
}

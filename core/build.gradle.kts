import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.research.kex-base")
    kotlin("plugin.serialization") version `kotlin-version`
}

dependencies {
    implementation(kfg())
    implementation(project(":kex-annotation-processor"))
    implementation(kotlinx("serialization-json-jvm", `serialization-version`))
    testImplementation(project(":kex-test"))
}

description = "core"


tasks {
    withType<KotlinCompile> {
        kotlinOptions.freeCompilerArgs += "-Xopt-in=kotlin.RequiresOptIn"
    }
}

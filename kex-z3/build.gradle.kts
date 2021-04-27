import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("org.jetbrains.research.kex-base")
    kotlin("plugin.serialization") version `kotlin-version`
    kotlin("kapt")
}
dependencies {
    implementation(project(":core"))
    kapt(project(":kex-annotation-processor"))
    implementation(project(":kex-annotation-processor"))
    implementation("org.jetbrains.research:kfg:${`kfg-version`}")

    implementation("com.beust:klaxon:3.0.6")
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json-jvm:${`serialization-version`}")
    implementation("com.charleskorn.kaml:kaml-jvm:0.29.0")
    implementation("ru.spbstu:ktuples:0.0.1.11")
    implementation("com.github.saloed:custom-diff:0.0.6")
    implementation("name.fraser.neil.plaintext:diff_match_patch:master")

//    implementation("com.microsoft:z3:4.8.10-function-calls-0.2")
    implementation(files("/home/sobol/CLionProjects/z3/cmake-build-debug/com.microsoft.z3-4.8.10.0.jar"))

    testImplementation(project(":core").dependencyProject.sourceSets["test"].output)
}

description = "kex-z3"

kapt {
    annotationProcessors(
        "org.jetbrains.research.kex.smt.SMTProcessor",
        "org.jetbrains.research.kex.smt.SolverInfoProcessor"
    )
    arguments {
        arg("kex.templates", rootDir.resolve("velocity-templates"))
        arg("runner.resources", rootDir.resolve("kex-runner/src/main/resources"))
    }
}


tasks {
    withType<KotlinCompile> {
        kotlinOptions.freeCompilerArgs += "-Xopt-in=kotlin.RequiresOptIn"
    }
}

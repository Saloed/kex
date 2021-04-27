plugins {
    id("org.jetbrains.research.kex-base")
}

dependencies {
    implementation(project(":core"))
    implementation(project(":kex-annotation-processor"))
//    implementation(project(":kex-boolector"))
    implementation(project(":kex-z3"))
    implementation("org.jetbrains.research:kfg:${`kfg-version`}")

    implementation("commons-cli:commons-cli:1.4")
    implementation("commons-lang:commons-lang:2.6")
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.3.9")
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json-jvm:${`serialization-version`}")
    implementation("org.jeasy:easy-random-core:4.0.0")
    implementation("com.github.h0tk3y:better-parse:0.3.2")
    implementation("org.reflections:reflections:0.9.11")
    implementation("com.beust:klaxon:3.0.6")
    implementation("ru.spbstu:ktuples:0.0.1.11")

    testImplementation(project(":kex-test"))
    testImplementation(project(":core").dependencyProject.sourceSets["test"].output)
}

description = "kex-runner"

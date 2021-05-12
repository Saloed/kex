plugins {
    id("org.jetbrains.research.kex-base")
}

dependencies {
    implementation(project(":core"))
    implementation(project(":kex-annotation-processor"))
//    implementation(project(":kex-boolector"))
    implementation(project(":kex-z3"))
    implementation(kfg())

    implementation(kotlinx("coroutines-core", `coroutines-version`))
    implementation(kotlinx("serialization-json-jvm", `serialization-version`))
    implementation("com.beust:klaxon:${`klaxon-version`}")

    implementation("commons-cli:commons-cli:1.4")
    implementation("commons-lang:commons-lang:2.6")
    implementation("org.jeasy:easy-random-core:4.0.0")
    implementation("com.github.h0tk3y:better-parse:0.3.2")
    implementation("org.reflections:reflections:0.9.11")

    testImplementation(project(":kex-test"))
    testImplementation(project(":core").tests())
}

description = "kex-runner"

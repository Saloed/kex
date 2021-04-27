plugins {
    id("org.jetbrains.research.kex-base")
    kotlin("kapt")
}

dependencies {
    implementation(project(":core"))
    kapt(project(":kex-annotation-processor"))
    implementation(project(":kex-annotation-processor"))
    implementation("org.jetbrains.research:kfg:${`kfg-version`}")
    implementation("com.github.AbdullinAM:boolector-java:3.2.1")
    testImplementation(project(":core").dependencyProject.sourceSets["test"].output)
}

description = "kex-boolector"

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

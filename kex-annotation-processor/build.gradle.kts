plugins {
    id("org.jetbrains.research.kex-base")
}

dependencies {
    implementation("org.apache.velocity:velocity:1.7")
    implementation("com.beust:klaxon:${`klaxon-version`}")
}

description = "kex-annotation-processor"

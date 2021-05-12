plugins {
    `kotlin-dsl`
}

val kotlinVersion = "1.5.0" // todo: remove this

repositories {
    gradlePluginPortal()
    mavenCentral()
    jcenter()
}

dependencies {
    implementation("org.jetbrains.kotlin:kotlin-gradle-plugin:${kotlinVersion}")
}

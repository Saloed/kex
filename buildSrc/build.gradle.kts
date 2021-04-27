plugins {
    `kotlin-dsl`
}

val kotlinVersion = "1.4.30" // todo: remove this

repositories {
    gradlePluginPortal()
    mavenCentral()
    jcenter()
}

dependencies {
    implementation("org.jetbrains.kotlin:kotlin-gradle-plugin:${kotlinVersion}")
}

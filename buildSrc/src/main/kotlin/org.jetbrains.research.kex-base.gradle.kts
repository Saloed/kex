import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import java.util.Properties

plugins {
    kotlin("jvm")
    `java-library`
}

val githubProperties = Properties().apply { load(rootProject.file("github.properties").inputStream()) }
fun githubProperty(key: String) =
    githubProperties.getProperty(key)?.ifBlank { null } ?: System.getenv(key.replace(".", "_"))

fun MavenArtifactRepository.github(path: String) {
    url = uri(path)
    credentials {
        username = githubProperty("gpr.user")
        password = githubProperty("gpr.key")
    }
}

repositories {
    mavenCentral()
    mavenLocal()
    maven {
        url = uri("https://dl.bintray.com/cbeust/maven")
    }

    maven {
        url = uri("https://kotlin.bintray.com/kotlinx")
    }

    maven {
        url = uri("https://dl.bintray.com/abdullin/maven")
    }

    maven {
        url = uri("https://dl.bintray.com/kotlin/kotlin-eap")
    }

    maven {
        url = uri("https://dl.bintray.com/vorpal-research/kotlin-maven")
    }

    maven {
        url = uri("https://repo.maven.apache.org/maven2/")
    }

    maven {
        url = uri("https://jitpack.io")
    }

    maven { github("https://maven.pkg.github.com/saloed/kfg") }
    maven { github("https://maven.pkg.github.com/saloed/z3") }
    maven { github("https://maven.pkg.github.com/saloed/custom-diff") }
    maven { github("https://maven.pkg.github.com/saloed/diff-match-patch") }
}

dependencies {
    implementation(kotlin("stdlib", `kotlin-version`))
    implementation(kotlin("reflect", `kotlin-version`))
    implementation("org.ini4j:ini4j:${`ini4j-version`}")
    implementation("org.slf4j:slf4j-api:${`slf4j-version`}")
    implementation("ch.qos.logback:logback-classic:${`logback-version`}")
    implementation("com.abdullin:kt-helper:${`kt-helper-version`}")
    testImplementation(kotlin("test-junit5", `kotlin-version`))
    testImplementation("org.junit.jupiter:junit-jupiter:5.7.1")
    testRuntimeOnly("org.junit.jupiter:junit-jupiter-engine:5.7.1")
}

group = "org.jetbrains.research"
version = "0.0.1"
java.sourceCompatibility = JavaVersion.VERSION_11

tasks {
    withType<JavaCompile> {
        options.encoding = "UTF-8"
    }
    withType<JavaCompile> {
        sourceCompatibility = "11"
        targetCompatibility = "11"
    }
    withType<KotlinCompile> {
        kotlinOptions.jvmTarget = "11"
    }
    withType<Test> {
        useJUnitPlatform()
    }
}

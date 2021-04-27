plugins {
    id("org.jetbrains.research.kex-base")
}

description = "kex-test"

val fatJar = task("fatJar", type = Jar::class) {
    archiveBaseName.set("${archiveBaseName.get()}-jar-with-dependencies")
    from(configurations.runtimeClasspath.get().map { if (it.isDirectory) it else zipTree(it) })
    with(tasks.jar.get() as CopySpec)
}

tasks {
    "build" {
        dependsOn(fatJar)
    }
}

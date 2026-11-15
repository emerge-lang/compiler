package io.github.tmarsteel.emerge.integrationtests

import java.nio.file.Path
import java.nio.file.Paths
import java.util.concurrent.TimeUnit
import kotlin.io.path.exists
import kotlin.io.path.isRegularFile

/**
 * The built toolchain to test, and how to run what it produces for [TARGET] on this machine.
 */
class TestEnvironment private constructor(
    val programsDirectory: Path,
    val workDirectory: Path,
    val javaExecutable: Path,
    val toolchainJar: Path,
    val toolchainConfig: Path,
    val executor: Executor,
) {
    /** How to run a linux binary on this machine */
    enum class Executor {
        NATIVE,
        WSL,
        ;

        fun commandFor(binary: Path): List<String> = when (this) {
            NATIVE -> listOf(binary.toAbsolutePath().toString())
            // wsl.exe translates the working directory of the process, so the path is given relative to that
            WSL -> listOf("wsl.exe", "-e", "./" + binary.fileName.toString())
        }
    }

    sealed interface Detection {
        class Available(val environment: TestEnvironment) : Detection
        class Unavailable(val reason: String) : Detection
    }

    companion object {
        const val TARGET = "x86_64-pc-linux-gnu"
        const val PROPERTY_TOOLCHAIN_DIR = "emerge.integration-tests.toolchain-dir"
        const val PROPERTY_OPTIONAL = "emerge.integration-tests.optional"

        /** if true, an environment that cannot run the tests is a reason to skip them rather than a failure */
        val isOptional: Boolean get() = System.getProperty(PROPERTY_OPTIONAL).toBoolean()

        fun detect(): Detection {
            val repositoryRoot = requiredPath("emerge.integration-tests.repository-root")
            val programsDirectory = requiredPath("emerge.integration-tests.programs")
            val workDirectory = requiredPath("emerge.integration-tests.work-directory")
            val currentJava = Path.of(System.getProperty("java.home"), "bin", "java")

            val toolchainDirectory = System.getProperty(PROPERTY_TOOLCHAIN_DIR)
                ?.takeUnless { it.isBlank() }
                ?.let { Paths.get(it).toAbsolutePath().normalize() }

            val javaExecutable: Path
            val toolchainJar: Path
            val toolchainConfig: Path
            val howToFix: String
            if (toolchainDirectory != null) {
                // an installed toolchain, laid out like the distributable archives
                toolchainJar = toolchainDirectory.resolve("bin").resolve("toolchain.jar")
                toolchainConfig = toolchainDirectory.resolve("toolchain-config.yml")
                javaExecutable = sequenceOf("java", "java.exe")
                    .map { toolchainDirectory.resolve("jre").resolve("bin").resolve(it) }
                    .firstOrNull { it.isRegularFile() }
                    ?: currentJava
                howToFix = "$PROPERTY_TOOLCHAIN_DIR must point to an installed toolchain"
            } else {
                // the toolchain as built in this working copy
                toolchainJar = repositoryRoot.resolve("toolchain").resolve("target").resolve("toolchain.jar")
                toolchainConfig = repositoryRoot.resolve("toolchain-config.yml")
                javaExecutable = currentJava
                howToFix = "build the toolchain module and create the configuration from toolchain-config.yml.dist, or set $PROPERTY_TOOLCHAIN_DIR to an installed toolchain"
            }

            for (file in listOf(toolchainJar, toolchainConfig)) {
                if (!file.exists()) {
                    return Detection.Unavailable("$file does not exist; $howToFix")
                }
            }

            val executor = detectExecutor()
                ?: return Detection.Unavailable("found no way to run a linux binary: this is not x86_64 linux, and wsl.exe is not usable")

            return Detection.Available(TestEnvironment(
                programsDirectory,
                workDirectory,
                javaExecutable,
                toolchainJar,
                toolchainConfig,
                executor,
            ))
        }

        private fun requiredPath(property: String): Path {
            val value = System.getProperty(property) ?: error("Missing system property $property; it is set in the pom.xml")
            return Paths.get(value).toAbsolutePath().normalize()
        }

        private fun detectExecutor(): Executor? {
            val osName = System.getProperty("os.name").lowercase()
            val osArch = System.getProperty("os.arch").lowercase()
            if ("linux" in osName && osArch in setOf("amd64", "x86_64")) {
                return Executor.NATIVE
            }

            if ("windows" in osName) {
                val wslWorks = try {
                    val process = ProcessBuilder("wsl.exe", "-e", "true")
                        .redirectErrorStream(true)
                        .redirectOutput(ProcessBuilder.Redirect.DISCARD)
                        .start()
                    if (process.waitFor(60, TimeUnit.SECONDS)) {
                        process.exitValue() == 0
                    } else {
                        process.destroyForcibly()
                        false
                    }
                } catch (_: java.io.IOException) {
                    false
                }
                if (wslWorks) {
                    return Executor.WSL
                }
            }

            return null
        }
    }
}

package io.github.tmarsteel.emerge.integrationtests

import java.nio.file.Files
import java.nio.file.Path
import java.util.concurrent.TimeUnit
import kotlin.io.path.createDirectories
import kotlin.io.path.exists
import kotlin.io.path.isDirectory
import kotlin.io.path.name
import kotlin.io.path.readText
import kotlin.io.path.writeText

/**
 * One directory below `programs`: the module `<name>` with its sources in `src`, and what running it must result in.
 */
class EmergeProgram(val directory: Path) {
    val name: String = directory.name
    val sourceDirectory: Path = directory.resolve("src")
    val expectedStdout: String get() = directory.resolve(EXPECTED_STDOUT_FILE).readText().normalizeLineEndings()
    val expectedExitCode: Int get() = directory.resolve(EXPECTED_EXIT_CODE_FILE)
        .takeIf { it.exists() }
        ?.readText()?.trim()?.toInt()
        ?: 0

    class ProcessResult(val exitCode: Int, val stdout: String, val stderr: String)

    /**
     * Runs the built toolchain the way a user does.
     * @return the result of the compiler, and where it put the binary
     */
    fun compile(environment: TestEnvironment): Pair<ProcessResult, Path> {
        val workDirectory = environment.workDirectory.resolve(name)
        val outputDirectory = workDirectory.resolve("out")
        outputDirectory.toFile().deleteRecursively()
        outputDirectory.createDirectories()

        val projectConfig = workDirectory.resolve("emerge-build.yml")
        projectConfig.writeText("""
            modules:
              - name: $name
                sources: ${sourceDirectory.yamlString()}
            targets:
              ${TestEnvironment.TARGET}:
                output-directory: ${outputDirectory.yamlString()}
        """.trimIndent())

        val result = run(
            listOf(
                environment.javaExecutable.toString(),
                "-jar", environment.toolchainJar.toString(),
                "--toolchain-config", environment.toolchainConfig.toString(),
                "project",
                "--project-config", projectConfig.toString(),
                "compile",
                "--target", TestEnvironment.TARGET,
            ),
            workDirectory,
            COMPILE_TIMEOUT_SECONDS,
        )

        return Pair(result, outputDirectory.resolve("runnable"))
    }

    fun execute(environment: TestEnvironment, binary: Path): ProcessResult {
        return run(environment.executor.commandFor(binary), binary.parent, RUN_TIMEOUT_SECONDS)
    }

    private fun run(command: List<String>, workingDirectory: Path, timeoutSeconds: Long): ProcessResult {
        val stdoutFile = Files.createTempFile("emerge-integration-test", ".stdout")
        val stderrFile = Files.createTempFile("emerge-integration-test", ".stderr")
        try {
            val process = ProcessBuilder(command)
                .directory(workingDirectory.toFile())
                .redirectInput(ProcessBuilder.Redirect.from(NULL_DEVICE))
                .redirectOutput(stdoutFile.toFile())
                .redirectError(stderrFile.toFile())
                .start()
            if (!process.waitFor(timeoutSeconds, TimeUnit.SECONDS)) {
                process.destroyForcibly()
                throw AssertionError("`${command.joinToString(" ")}` did not finish within $timeoutSeconds seconds")
            }

            return ProcessResult(
                process.exitValue(),
                stdoutFile.readText().normalizeLineEndings(),
                stderrFile.readText().normalizeLineEndings(),
            )
        } finally {
            Files.deleteIfExists(stdoutFile)
            Files.deleteIfExists(stderrFile)
        }
    }

    override fun toString() = name

    companion object {
        const val EXPECTED_STDOUT_FILE = "expected-stdout.txt"
        const val EXPECTED_EXIT_CODE_FILE = "expected-exit-code.txt"
        private const val COMPILE_TIMEOUT_SECONDS = 300L
        private const val RUN_TIMEOUT_SECONDS = 60L
        private val NULL_DEVICE = java.io.File(if ("windows" in System.getProperty("os.name").lowercase()) "NUL" else "/dev/null")

        fun discover(programsDirectory: Path): List<EmergeProgram> {
            return Files.list(programsDirectory).use { entries ->
                entries
                    .filter { it.isDirectory() }
                    .map(::EmergeProgram)
                    .toList()
                    .sortedBy { it.name }
            }
        }

        private fun String.normalizeLineEndings() = replace("\r\n", "\n")
        private fun Path.yamlString() = "\"" + toAbsolutePath().toString().replace('\\', '/') + "\""
    }
}

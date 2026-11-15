package io.github.tmarsteel.emerge.integrationtests

import io.kotest.assertions.fail
import io.kotest.assertions.withClue
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldNotBeEmpty
import io.kotest.matchers.shouldBe
import java.nio.file.Paths
import kotlin.io.path.exists

class ProgramTests : FreeSpec({
    val detection = TestEnvironment.detect()
    val environment = (detection as? TestEnvironment.Detection.Available)?.environment
    val programs = EmergeProgram.discover(Paths.get(System.getProperty("emerge.integration-tests.programs")))

    "environment" {
        programs.shouldNotBeEmpty()
        if (detection is TestEnvironment.Detection.Unavailable) {
            val message = "Cannot run the ${programs.size} emerge programs: ${detection.reason}"
            if (!TestEnvironment.isOptional) {
                fail("$message\nSet -D${TestEnvironment.PROPERTY_OPTIONAL}=true to skip them instead.")
            }
            println("SKIPPED: $message")
        }
    }

    for (program in programs) {
        program.name.config(enabled = environment != null) {
            environment!!
            withClue("${program.directory.resolve(EmergeProgram.EXPECTED_STDOUT_FILE)} is missing") {
                program.directory.resolve(EmergeProgram.EXPECTED_STDOUT_FILE).exists() shouldBe true
            }

            val (compilation, binary) = program.compile(environment)
            if (compilation.exitCode != 0 || !binary.exists()) {
                fail("${program.name} did not compile (exit code ${compilation.exitCode}):\n${compilation.stdout}\n${compilation.stderr}")
            }

            val execution = program.execute(environment, binary)
            withClue("stderr of ${program.name}:\n${execution.stderr}") {
                execution.stdout shouldBe program.expectedStdout
                execution.exitCode shouldBe program.expectedExitCode
            }
        }
    }
})

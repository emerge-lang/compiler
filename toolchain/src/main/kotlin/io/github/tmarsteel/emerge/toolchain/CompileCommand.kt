package io.github.tmarsteel.emerge.toolchain

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.CliktError
import com.github.ajalt.clikt.core.PrintMessage
import com.github.ajalt.clikt.core.requireObject
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.options.validate
import com.github.ajalt.clikt.parameters.types.choice
import compiler.InternalCompilerError
import compiler.binding.context.SoftwareContext
import compiler.lexer.SourceSet
import compiler.lexer.lex
import compiler.parser.SourceFileRule
import compiler.parser.grammar.rule.MatchingResult
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.ModuleWithoutSourcesDiagnostic
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.common.EmergeConstants
import io.github.tmarsteel.emerge.common.config.ConfigModuleDefinition
import io.github.tmarsteel.emerge.toolchain.config.ProjectConfig
import io.github.tmarsteel.emerge.toolchain.config.ToolchainConfig
import java.time.Clock
import java.time.Duration
import java.time.Instant
import kotlin.time.toKotlinDuration

object CompileCommand : CliktCommand() {
    private val toolchainConfig by requireObject<ToolchainConfig>()
    private val projectConfig by requireObject<ProjectConfig>()

    private val target by option("--target")
        .choice(backends)
        .required()
        .validate {
            require(it in projectConfig.targets) {
                "Target ${it.targetName} is not configured for the project"
            }
        }

    override fun run() {
        val toolchainConfigForBackend = toolchainConfig.backendConfigs[target]
            ?: throw CliktError("Missing toolchain configuration for target ${target.targetName}")
        val projectConfigForBackend = projectConfig.targets[target]
            ?: throw CliktError("Missing project configuration for target ${target.targetName}")
        val typeunsafeTarget = target as EmergeBackend<in Any, in Any>

        val swCtx = SoftwareContext()

        val measureClock = Clock.systemUTC()
        val startedAt = measureClock.instant()

        val modulesToLoad = listOf(
            ConfigModuleDefinition(EmergeConstants.STD_MODULE_NAME, toolchainConfig.frontend.stdModuleSources),
            ConfigModuleDefinition(EmergeConstants.CORE_MODULE_NAME, toolchainConfig.frontend.coreModuleSources),
        ) + projectConfig.modules + typeunsafeTarget.getTargetSpecificModules(toolchainConfigForBackend, projectConfigForBackend)
        var anyParseErrors = false
        for (moduleRef in modulesToLoad) {
            val moduleContext = swCtx.registerModule(moduleRef.name, moduleRef.uses)
            SourceSet.load(moduleRef.sourceDirectory, moduleRef.name)
                .also {
                    if (it.isEmpty()) {
                        echo(ModuleWithoutSourcesDiagnostic(moduleRef.name, moduleRef.sourceDirectory))
                    }
                }
                .map { SourceFileRule.match(lex(it), it) }
                .forEach { fileResult ->
                    when (fileResult) {
                        is MatchingResult.Success -> moduleContext.addSourceFile(fileResult.item)
                        is MatchingResult.Error -> {
                            echo(fileResult.reporting)
                            anyParseErrors = true
                        }
                    }
                }
        }

        val lexicalCompleteAt = measureClock.instant()

        if (anyParseErrors) {
            throw PrintMessage(
                "Could not parse the source-code",
                statusCode = 1,
                printError = true,
            )
        }

        val diagnosis = ProcessOnTheGoDiagnosis {
            if (it.severity > Diagnostic.Severity.CONSECUTIVE) {
                echo(it)
            }
        }
        swCtx.doSemanticAnalysis(diagnosis)
        val semanticCompleteAt = measureClock.instant()

        if (diagnosis.nErrors > 0uL) {
            throw PrintMessage(
                "The provided program is not valid",
                statusCode = 1,
                printError = true,
            )
        }

        val irSwCtx = swCtx.toBackendIr()
        val backendStartedAt = measureClock.instant()
        try {
            typeunsafeTarget.emit(toolchainConfigForBackend, projectConfigForBackend, irSwCtx)
        } catch (ex: CodeGenerationException) {
            echo("The backend failed to generate code.")
            throw ex
        }
        val backendDoneAt = measureClock.instant()

        echo("----------")
        echo("lexical analysis: ${elapsedBetween(startedAt, lexicalCompleteAt)}")
        echo("semantic analysis: ${elapsedBetween(lexicalCompleteAt, semanticCompleteAt)}")
        echo("backend: ${elapsedBetween(backendStartedAt, backendDoneAt)}")
        echo("total time: ${elapsedBetween(startedAt, backendDoneAt)}")
    }

    private fun echo(diagnostic: Diagnostic) {
        echo(diagnostic.toString())
        echo()
        echo()
    }
}

fun main(args: Array<String>) {
    if (backends.isEmpty()) {
        throw InternalCompilerError("No backends found!")
    }
    CompileCommand.main(args)
}

private val Iterable<Diagnostic>.containsErrors
    get() = map(Diagnostic::severity).any { it.level >= Diagnostic.Severity.ERROR.level }

private fun elapsedBetween(start: Instant, end: Instant): String {
    val duration = Duration.between(start, end).toKotlinDuration()
    // there is no function that automatically chooses the right unit AND limits fractional digits
    // so we'll use toString() to pick the unit, and some regex magic to limit to 3 fractional digits, not rounding
    return duration.toString()
        .replace(Regex("(?<=\\.\\d{3})\\d+"), "")
        .replace(".000", "")
}

private class ProcessOnTheGoDiagnosis(private val process: (Diagnostic) -> Unit) : Diagnosis {
    private val seen = HashSet<Diagnostic>()
    override var nErrors: ULong = 0uL
        private set

    override fun add(finding: Diagnostic) {
        if (finding.severity >= Diagnostic.Severity.ERROR) {
            nErrors++
        }

        if (seen.add(finding)) {
            process(finding)
        }
    }

    override fun hasSameDrainAs(other: Diagnosis): Boolean {
        return other === this || other.hasSameDrainAs(this)
    }
}
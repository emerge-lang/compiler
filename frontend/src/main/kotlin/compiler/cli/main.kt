package compiler.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.PrintMessage
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.defaultLazy
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.path
import compiler.CoreIntrinsicsModule
import compiler.InternalCompilerError
import compiler.StandardLibraryModule
import compiler.binding.context.SoftwareContext
import compiler.lexer.SourceSet
import compiler.lexer.lex
import compiler.parser.SourceFileRule
import compiler.parser.grammar.rule.MatchingResult
import compiler.reportings.ModuleWithoutSourcesReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import java.nio.file.Path
import java.time.Clock
import java.time.Duration
import java.time.Instant
import java.util.ServiceLoader
import java.util.stream.Collectors
import kotlin.io.path.createDirectories
import kotlin.time.toKotlinDuration

private val backends: Map<String, EmergeBackend> = ServiceLoader.load(EmergeBackend::class.java)
    .stream()
    .map { it.get() }
    .collect(Collectors.toMap(
        { it.targetName },
        { it },
        { a, b -> throw InternalCompilerError("Found two backends with name ${a.targetName}: ${a::class.qualifiedName} and ${b::class.qualifiedName}")}
    ))

object CompileCommand : CliktCommand() {
    private val moduleName: CanonicalElementName.Package by argument("module name").packageName()
    private val srcDir: Path by argument("source directory")
        .path(mustExist = true, canBeFile = false, canBeDir = true, mustBeReadable = true)
    private val outDir: Path by argument("output directory")
        .path(mustExist = false, canBeFile = false, mustBeWritable = true)
        .defaultLazy(defaultForHelp = "<source dir>/../emerge-out") {
            srcDir.toAbsolutePath().parent.resolve("emerge-out")
        }
    private val target: EmergeBackend by option("--target").selectFrom(backends).required()

    override fun run() {
        val swCtx = SoftwareContext()

        val measureClock = Clock.systemUTC()
        val startedAt = measureClock.instant()

        val modulesToLoad = target.targetSpecificModules + listOf(
            ModuleSourceRef(CoreIntrinsicsModule.SRC_DIR, CoreIntrinsicsModule.NAME),
            ModuleSourceRef(StandardLibraryModule.SRC_DIR, StandardLibraryModule.NAME),
            ModuleSourceRef(srcDir, moduleName)
        )
        var anyParseErrors = false
        for (moduleRef in modulesToLoad) {
            val moduleContext = swCtx.registerModule(moduleRef.moduleName)
            SourceSet.load(moduleRef.path, moduleRef.moduleName)
                .also {
                    if (it.isEmpty()) {
                        echo(ModuleWithoutSourcesReporting(moduleRef.moduleName, moduleRef.path))
                    }
                }
                .map { SourceFileRule.match(lex(it), it) }
                .forEach { fileResult ->
                    when (fileResult) {
                        is MatchingResult.Success -> moduleContext.addSourceFile(fileResult.item)
                        is MatchingResult.Error -> {
                            this.echo(fileResult.reporting)
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

        val semanticResults = swCtx.doSemanticAnalysis()
        val semanticCompleteAt = measureClock.instant()

        semanticResults
            .filter { it.level > Reporting.Level.CONSECUTIVE }
            .forEach(this::echo)

        if (semanticResults.any { it.level >= Reporting.Level.ERROR}) {
            throw PrintMessage(
                "The provided program is not valid",
                statusCode = 1,
                printError = true,
            )
        }

        outDir.createDirectories()
        val backendStartedAt = measureClock.instant()
        try {
            target.emit(swCtx.toBackendIr(), outDir)
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

    private fun echo(reporting: Reporting) {
        echo(reporting.toString())
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

private val Iterable<Reporting>.containsErrors
    get() = map(Reporting::level).any { it.level >= Reporting.Level.ERROR.level }

private fun elapsedBetween(start: Instant, end: Instant): String {
    val duration = Duration.between(start, end).toKotlinDuration()
    // there is no function that automatically chooses the right unit AND limits fractional digits
    // so we'll use toString() to pick the unit, and some regex magic to limit to 3 fractional digits, not rounding
    return duration.toString()
        .replace(Regex("(?<=\\.\\d{3})\\d+"), "")
        .replace(".000", "")
}
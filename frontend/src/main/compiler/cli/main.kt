package compiler.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.types.path
import compiler.CoreIntrinsicsModule
import compiler.PackageName
import compiler.binding.context.SoftwareContext
import compiler.lexer.SourceSet
import compiler.lexer.lex
import compiler.parser.SourceFileRule
import compiler.reportings.Reporting
import java.nio.file.Path
import java.time.Clock
import java.time.Duration
import java.time.Instant
import kotlin.time.toKotlinDuration

object CompileCommand : CliktCommand() {
    private val moduleName: PackageName by argument("module name").packageName()
    private val srcDir: Path by argument("source directory").path(mustExist = true, canBeFile = false, canBeDir = true, mustBeReadable = true)
    override fun run() {
        val swCtx = SoftwareContext()
        CoreIntrinsicsModule.addTo(swCtx)
        val moduleCtx = swCtx.registerModule(moduleName)

        val measureClock = Clock.systemUTC()
        val startedAt = measureClock.instant()
        val sourceInMemoryAt: Instant

        val parseResults = SourceSet.load(srcDir, moduleName)
            .also {
                sourceInMemoryAt = measureClock.instant()
            }
            .map {
                SourceFileRule.match(lex(it), it.packageName)
            }

        val lexicalCompleteAt = measureClock.instant()
        parseResults.flatMap { it.reportings }.forEach(this::echo)

        if (parseResults.any { it.reportings.containsErrors }) {
            return
        }
        if (parseResults.isEmpty()) {
            echo("Found no source files to compile!")
            return
        }

        parseResults.forEach {
            val bound = it.item!!.bindTo(moduleCtx)
            moduleCtx.addSourceFile(bound)
        }

        val semanticResults = swCtx.doSemanticAnalysis()
        val semanticCompleteAt = measureClock.instant()

        semanticResults.forEach(this::echo)

        echo("----------")
        echo("loading sources into memory: ${elapsedBetween(startedAt, sourceInMemoryAt)}")
        echo("lexical analysis: ${elapsedBetween(sourceInMemoryAt, lexicalCompleteAt)}")
        echo("semantic analysis: ${elapsedBetween(lexicalCompleteAt, semanticCompleteAt)}")
        echo("total time: ${elapsedBetween(startedAt, semanticCompleteAt)}")
    }

    private fun echo(reporting: Reporting) {
        echo(reporting.toString())
        echo()
        echo()
    }
}

fun main(args: Array<String>) {
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
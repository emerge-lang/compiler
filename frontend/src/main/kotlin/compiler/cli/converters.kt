package compiler.cli

import com.github.ajalt.clikt.completion.CompletionCandidates
import com.github.ajalt.clikt.core.BadParameterValue
import com.github.ajalt.clikt.parameters.arguments.ProcessedArgument
import com.github.ajalt.clikt.parameters.arguments.RawArgument
import com.github.ajalt.clikt.parameters.arguments.convert
import com.github.ajalt.clikt.parameters.options.NullableOption
import com.github.ajalt.clikt.parameters.options.RawOption
import com.github.ajalt.clikt.parameters.options.convert
import compiler.lexer.MemorySourceFile
import compiler.lexer.lex
import compiler.parser.grammar.ModuleOrPackageName
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

fun RawArgument.packageName(): ProcessedArgument<CanonicalElementName.Package, CanonicalElementName.Package> {
    return convert { rawName ->
        val parseResult = ModuleOrPackageName.match(lex(MemorySourceFile("CLI argument ${this.name}", CanonicalElementName.Package(listOf("cli")), rawName)))
        parseResult.reportings.find { it.level > Reporting.Level.ERROR }?.let {
            fail(it.message)
        }

        CanonicalElementName.Package(parseResult.item!!.names.map { it.value })
    }
}

fun <Out : Any> RawOption.selectFrom(source: Map<String, Out>): NullableOption<Out, Out> {
    return convert(completionCandidates = explicitCompletionCandidates ?: CompletionCandidates.Fixed(source.keys)) {rawKey ->
        source[rawKey]
            ?: throw BadParameterValue("$rawKey is not a valid value for $name. Options: ${source.keys.sorted().joinToString()}")
    }
}
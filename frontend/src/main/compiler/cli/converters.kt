package compiler.cli

import com.github.ajalt.clikt.parameters.arguments.ProcessedArgument
import com.github.ajalt.clikt.parameters.arguments.RawArgument
import com.github.ajalt.clikt.parameters.arguments.convert
import compiler.PackageName
import compiler.lexer.MemorySourceFile
import compiler.lexer.lex
import compiler.parser.grammar.ModuleOrPackageName
import compiler.parser.grammar.rule.MatchingContext
import compiler.reportings.Reporting

fun RawArgument.packageName(): ProcessedArgument<PackageName, PackageName> {
    return convert { rawName ->
        val parseResult = ModuleOrPackageName.match(MatchingContext.None, lex(MemorySourceFile("CLI argument ${this.name}", PackageName(emptyList()), rawName)))
        parseResult.reportings.find { it.level > Reporting.Level.ERROR }?.let {
            fail(it.message)
        }

        PackageName(parseResult.item!!.names.map { it.value })
    }
}
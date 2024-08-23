package compiler.util

import compiler.InternalCompilerError
import compiler.ast.ASTSourceFile
import compiler.lexer.ClasspathSourceFile
import compiler.lexer.lex
import compiler.parser.SourceFileRule
import compiler.parser.grammar.rule.MatchingResult
import io.github.tmarsteel.emerge.common.CanonicalElementName
import java.nio.file.Path
import java.nio.file.Paths

fun parseFromClasspath(path: String, packageName: CanonicalElementName.Package): ASTSourceFile =
    parseFromClasspath(Paths.get(path), packageName)

fun parseFromClasspath(path: Path, packageName: CanonicalElementName.Package): ASTSourceFile {
    val sourceFile = ClasspathSourceFile(
        path,
        packageName,
        ClassLoader.getSystemResource(path.toString())!!.readText(),
    )

    val matchResult = SourceFileRule.match(lex(sourceFile), sourceFile)
    when (matchResult) {
        is MatchingResult.Success -> return matchResult.item
        is MatchingResult.Error -> {
            System.err.println()
            System.err.println()
            System.err.println("----------------------------------")
            System.err.println("Errors while parsing from classpath:")
            System.err.println(matchResult.reporting)
            throw InternalCompilerError("Failed to parse from classpath $path")
        }
    }
}
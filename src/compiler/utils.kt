package compiler

import Module
import compiler.ast.context.Module
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.parser.TokenSequence
import java.nio.file.Path
import java.nio.file.Paths

public fun parseFromClasspath(path: String): Module = parseFromClasspath(Paths.get(path))

public fun parseFromClasspath(path: Path): Module {
    val sourceode = ClassLoader.getSystemResource(path.toString()).readText().lines()

    val sourceDescriptor = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "classpath:" + path
        override val sourceLines = sourceode
    }
    val matchResult = Module.tryMatch(TokenSequence(lex(sourceDescriptor).toList()))

    matchResult.errors.forEach(::println)

    return matchResult.result ?: throw InternalCompilerError("Failed to parse from classpath $path")
}
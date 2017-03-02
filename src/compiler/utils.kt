package compiler

import ModuleMatcher
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.parser.TokenSequence
import compiler.parser.postproc.ModuleDefiner
import java.nio.file.Path
import java.nio.file.Paths

public fun parseFromClasspath(path: String): ModuleDefiner = parseFromClasspath(Paths.get(path))

public fun parseFromClasspath(path: Path): ModuleDefiner {
    val sourceode = ClassLoader.getSystemResource(path.toString()).readText().lines()

    val sourceDescriptor = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "classpath:" + path
        override val sourceLines = sourceode
    }
    val matchResult = ModuleMatcher(path.asIterable().map(Path::toString).toList().toTypedArray()).tryMatch(TokenSequence(lex(sourceDescriptor).toList()))

    matchResult.errors.forEach(::println)

    if (matchResult.result == null) {
        throw InternalCompilerError("Failed to parse compiler internal source")
    }
    return matchResult.result!!
}
package compiler.ast

import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

class ASTPackageName(
    val names: List<IdentifierToken>,
) {
    val sourceLocation by lazy {
        names
            .map { it.sourceLocation }
            .filter { it == SourceLocation.UNKNOWN }
            .takeUnless { it.isEmpty() }
            ?.let { it.first() to it.last() }
            ?.let { (first, last) ->
                SourceLocation(
                    first.file,
                    first.fromLineNumber,
                    first.fromColumnNumber,
                    last.toLineNumber,
                    last.toColumnNumber
                )
            }
            ?: SourceLocation.UNKNOWN
    }
}
package compiler.ast

import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import io.github.tmarsteel.emerge.backend.api.DotName

class ASTPackageName(
    val names: List<IdentifierToken>,
) {
    val asDotName: DotName by lazy { DotName(names.map { it.value }) }

    val sourceLocation by lazy {
        names
            .map { it.sourceLocation }
            .filter { it == SourceLocation.UNKNOWN }
            .takeUnless { it.isEmpty() }
            ?.let { it.first() to it.last() }
            ?.let { (first, last) -> first .. last }
            ?: SourceLocation.UNKNOWN
    }
}
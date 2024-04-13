package compiler.ast

import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

class AstPackageName(
    val names: List<IdentifierToken>,
) {
    val asCanonical: CanonicalElementName.Package by lazy { CanonicalElementName.Package(names.map { it.value }) }

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
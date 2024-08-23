package compiler.ast

import compiler.lexer.IdentifierToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

class AstPackageName(
    val names: List<IdentifierToken>,
) {
    val asCanonical: CanonicalElementName.Package by lazy { CanonicalElementName.Package(names.map { it.value }) }

    val span by lazy {
        names
            .map { it.span }
            .filterNot { it == Span.UNKNOWN }
            .takeUnless { it.isEmpty() }
            ?.let { it.first() to it.last() }
            ?.let { (first, last) -> first .. last }
            ?: Span.UNKNOWN
    }
}
package compiler.reportings

import compiler.ast.type.NamedTypeReference
import compiler.lexer.Span

class DuplicateSupertypeReporting(
    val supertype: NamedTypeReference,
) : Reporting(
    Level.ERROR,
    "Can inherit from ${supertype.simpleName} only once",
    supertype.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is DuplicateSupertypeReporting) return false

        if (supertype.span != other.supertype.span) return false

        return true
    }

    override fun hashCode(): Int {
        return supertype.span.hashCode()
    }
}
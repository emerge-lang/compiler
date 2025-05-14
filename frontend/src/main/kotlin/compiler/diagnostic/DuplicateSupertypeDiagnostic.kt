package compiler.diagnostic

import compiler.ast.type.NamedTypeReference
import compiler.lexer.Span

class DuplicateSupertypeDiagnostic(
    val supertype: NamedTypeReference,
) : Diagnostic(
    Severity.ERROR,
    "Can inherit from ${supertype.simpleName} only once",
    supertype.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is DuplicateSupertypeDiagnostic) return false

        if (supertype.span != other.supertype.span) return false

        return true
    }

    override fun hashCode(): Int {
        return supertype.span.hashCode()
    }
}
package compiler.reportings

import compiler.ast.type.TypeReference
import compiler.lexer.Span

class DuplicateSupertypeDiagnostic(
    val supertype: TypeReference,
) : Diagnostic(
    Level.ERROR,
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
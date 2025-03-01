package compiler.reportings

import compiler.ast.type.TypeReference
import compiler.lexer.Span

class IllegalSupertypeDiagnostic(
    val supertype: TypeReference,
    reason: String,
) : Diagnostic(
    Level.ERROR,
    "Cannot inherit from this type: $reason",
    supertype.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IllegalSupertypeDiagnostic) return false

        if (supertype.span != other.supertype.span) return false

        return true
    }

    override fun hashCode(): Int {
        return supertype.span.hashCode()
    }
}
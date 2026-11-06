package compiler.diagnostic

import compiler.ast.type.AstSimpleTypeReference
import compiler.lexer.Span

class RedundantMutabilityOnSupertypeDiagnostic(
    val supertype: AstSimpleTypeReference,
    val reason: String,
) : Diagnostic(
    Severity.INFO,
    "${supertype.mutability} is redundant here: $reason",
    supertype.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is RedundantMutabilityOnSupertypeDiagnostic) return false

        if (supertype.span != other.supertype.span) return false

        return true
    }

    override fun hashCode(): Int {
        return supertype.span.hashCode()
    }
}
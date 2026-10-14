package compiler.diagnostic

import compiler.ast.type.AstSimpleTypeReference
import compiler.lexer.Span

class MutabilityOnSupertypeDiagnostic(
    val supertype: AstSimpleTypeReference,
) : Diagnostic(
    Severity.ERROR,
    "A supertype can only be declared const, making all instances of the subtype immutable; ${supertype.mutability} is not allowed here",
    supertype.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is MutabilityOnSupertypeDiagnostic) return false

        if (supertype.span != other.supertype.span) return false

        return true
    }

    override fun hashCode(): Int {
        return supertype.span.hashCode()
    }
}
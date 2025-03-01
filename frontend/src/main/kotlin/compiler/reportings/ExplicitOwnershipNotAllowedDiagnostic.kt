package compiler.reportings

import compiler.lexer.Token

class ExplicitOwnershipNotAllowedDiagnostic(
    val token: Token,
) : Diagnostic(
    Level.ERROR,
    "Declaring an ownership mode is only allowed on parameters, not on variables",
    token.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ExplicitOwnershipNotAllowedDiagnostic) return false

        if (token.span != other.token.span) return false

        return true
    }

    override fun hashCode(): Int {
        return token.span.hashCode()
    }
}
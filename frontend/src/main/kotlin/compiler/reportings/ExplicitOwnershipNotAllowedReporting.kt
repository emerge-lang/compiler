package compiler.reportings

import compiler.lexer.Token

class ExplicitOwnershipNotAllowedReporting(
    val token: Token,
) : Reporting(
    Level.ERROR,
    "Declaring an ownership mode is only allowed on parameters, not on variables",
    token.sourceLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ExplicitOwnershipNotAllowedReporting) return false

        if (token.sourceLocation != other.token.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        return token.sourceLocation.hashCode()
    }
}
package compiler.reportings

import compiler.lexer.Token

class ToplevelFunctionWithOverrideAttributeReporting(
    val overrideKeyword: Token,
) : Reporting(
    Level.ERROR,
    "Top-level functions cannot override (the concept of overriding only applies in interfaces and classes)",
    overrideKeyword.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ToplevelFunctionWithOverrideAttributeReporting) return false

        if (overrideKeyword != other.overrideKeyword) return false

        return true
    }

    override fun hashCode(): Int {
        return overrideKeyword.hashCode()
    }
}
package compiler.reportings

import compiler.ast.VariableDeclaration
import compiler.lexer.Span

class VariableUsedAfterLifetimeReporting(
    val variable: VariableDeclaration,
    val usageAt: Span,
    val lifetimeEndedAt: Span,
    /** If the lifetime hasn't _definitley_ ended, just might have */
    val lifetimeEndedMaybe: Boolean,
) : Reporting(
    Level.ERROR,
    run {
        val endedPhrase = if (lifetimeEndedMaybe) "might have ended" else "has ended"
        "The lifetime of variable ${variable.name.value} $endedPhrase, it cannot be used anymore"
    },
    usageAt,
) {
    override fun toString(): String {
        // TODO: single illustration with both locations if possible, just like rusts borrow errors.
        // Text rendering for that is not implemented yet

        var str = super.toString()
        str += "\nThe lifetime of ${variable.name.value} ended\nin $lifetimeEndedAt"

        return str
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is VariableUsedAfterLifetimeReporting) return false

        if (variable != other.variable) return false
        if (usageAt != other.usageAt) return false

        return true
    }

    override fun hashCode(): Int {
        var result = usageAt.hashCode()
        result = 31 * result + variable.hashCode()
        return result
    }
}
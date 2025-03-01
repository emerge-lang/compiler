package compiler.reportings

import compiler.ast.VariableDeclaration
import compiler.lexer.Span

class VariableUsedAfterLifetimeDiagnostic private constructor(
    val variable: VariableDeclaration,
    val usageAt: Span,
    val lifetimeEndedAt: Span,
    val lifetimeEndedMaybe: Boolean,
    private val endedPhrase: String,
) : Diagnostic(
    Level.ERROR,
    "Cannot use variable ${variable.name.value} after its lifetime $endedPhrase",
    usageAt,
) {
    constructor(
        variable: VariableDeclaration,
        usageAt: Span,
        lifetimeEndedAt: Span,
        /** If the lifetime hasn't _definitely_ ended, just might have */
        lifetimeEndedMaybe: Boolean,
    ) : this(
        variable,
        usageAt,
        lifetimeEndedAt,
        lifetimeEndedMaybe,
        if (lifetimeEndedMaybe) "might have ended" else "has ended",
    )
    override fun toString(): String {
        return levelAndMessage + "\nin " + illustrateHints(
            SourceHint(lifetimeEndedAt, "variable ${variable.name.value} is captured here, ending its lifetime", relativeOrderMatters = true),
            SourceHint(usageAt, "usage after lifetime $endedPhrase", relativeOrderMatters = true),
        )
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is VariableUsedAfterLifetimeDiagnostic) return false

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
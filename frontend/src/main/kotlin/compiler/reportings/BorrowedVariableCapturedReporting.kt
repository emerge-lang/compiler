package compiler.reportings

import compiler.ast.VariableDeclaration
import compiler.lexer.Span

class BorrowedVariableCapturedReporting(
    val variable: VariableDeclaration,
    captureAt: Span,
) : Reporting(
    Level.ERROR,
    "Cannot capture a borrowed value",
    captureAt,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is BorrowedVariableCapturedReporting) return false

        if (variable != other.variable) return false
        if (span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = variable.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }
}

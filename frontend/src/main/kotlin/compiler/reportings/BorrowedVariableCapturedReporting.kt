package compiler.reportings

import compiler.ast.VariableDeclaration
import compiler.lexer.SourceLocation

class BorrowedVariableCapturedReporting(
    val variable: VariableDeclaration,
    captureAt: SourceLocation,
) : Reporting(
    Level.ERROR,
    "Cannot capture a borrowed value",
    captureAt,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is BorrowedVariableCapturedReporting) return false

        if (variable != other.variable) return false
        if (sourceLocation != other.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        var result = variable.hashCode()
        result = 31 * result + sourceLocation.hashCode()
        return result
    }
}

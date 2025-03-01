package compiler.diagnostic

import compiler.ast.AstContinueExpression

class ContinueOutsideOfLoopDiagnostic(
    val breakStatement: AstContinueExpression,
) : Diagnostic(
    Severity.ERROR,
    "Continue statements must appear inside loops, this one is not in any loop.",
    breakStatement.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false
        if (!super.equals(other)) return false

        other as ContinueOutsideOfLoopDiagnostic

        return breakStatement == other.breakStatement
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + breakStatement.hashCode()
        return result
    }
}
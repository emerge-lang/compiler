package compiler.reportings

import compiler.ast.AstCodeChunk
import compiler.ast.Executable
import compiler.ast.Expression

data class ImplicitlyEvaluatedStatementDiagnostic(
    val statement: Executable,
) : Diagnostic(
    Level.ERROR,
    "A value must be given here (implicit evaluation)",
    statement.span,
) {
    init {
        require(statement !is Expression || (statement is AstCodeChunk && statement.statements.isEmpty()))
    }

    override fun toString() = super.toString()
}
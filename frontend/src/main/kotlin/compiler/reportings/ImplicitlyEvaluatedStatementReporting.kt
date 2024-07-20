package compiler.reportings

import compiler.ast.AstCodeChunk
import compiler.ast.Executable
import compiler.ast.Expression

data class ImplicitlyEvaluatedStatementReporting(
    val statement: Executable,
) : Reporting(
    Level.ERROR,
    "A value must be given here (implicit evaluation)",
    statement.span,
) {
    init {
        require(statement !is Expression || (statement is AstCodeChunk && statement.statements.isEmpty()))
    }

    override fun toString() = super.toString()
}
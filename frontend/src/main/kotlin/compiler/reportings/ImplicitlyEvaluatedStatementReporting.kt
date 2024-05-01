package compiler.reportings

import compiler.ast.Expression
import compiler.ast.Statement

data class ImplicitlyEvaluatedStatementReporting(
    val statement: Statement,
) : Reporting(
    Level.ERROR,
    "A value must be given here (implicit evaluation)",
    statement.span,
) {
    init {
        require(statement !is Expression)
    }

    override fun toString() = super.toString()
}
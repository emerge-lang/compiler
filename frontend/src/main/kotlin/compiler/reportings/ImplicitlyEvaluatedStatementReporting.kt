package compiler.reportings

import compiler.ast.Executable
import compiler.ast.expression.Expression

data class ImplicitlyEvaluatedStatementReporting(
    val statement: Executable<*>,
) : Reporting(
    Level.ERROR,
    "A value must be given here (implicit evaluation)",
    statement.sourceLocation,
) {
    init {
        require(statement !is Expression<*>)
    }

    override fun toString() = super.toString()
}
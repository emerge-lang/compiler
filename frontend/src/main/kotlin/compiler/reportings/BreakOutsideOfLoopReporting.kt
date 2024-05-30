package compiler.reportings

import compiler.ast.AstBreakStatement

class BreakOutsideOfLoopReporting(
    val breakStatement: AstBreakStatement,
) : Reporting(
    Level.ERROR,
    "Break statements must appear inside loops, this one is not in any loop.",
    breakStatement.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false
        if (!super.equals(other)) return false

        other as BreakOutsideOfLoopReporting

        return breakStatement == other.breakStatement
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + breakStatement.hashCode()
        return result
    }
}
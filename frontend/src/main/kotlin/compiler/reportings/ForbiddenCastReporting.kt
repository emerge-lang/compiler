package compiler.reportings

import compiler.ast.expression.AstCastExpression
import compiler.lexer.Span

class ForbiddenCastReporting(
    val castAt: AstCastExpression,
    reason: String,
    span: Span,
) : Reporting(
    Level.ERROR,
    reason,
    span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false
        if (!super.equals(other)) return false

        other as ForbiddenCastReporting

        return castAt.operator.span == other.castAt.operator.span
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + castAt.operator.span.hashCode()
        return result
    }
}
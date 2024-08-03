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

        return castAt.asToken.span == other.castAt.asToken.span
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + castAt.asToken.span.hashCode()
        return result
    }
}
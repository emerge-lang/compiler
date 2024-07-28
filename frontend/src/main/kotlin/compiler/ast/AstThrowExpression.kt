package compiler.ast

import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundThrowExpression
import compiler.lexer.KeywordToken
import compiler.lexer.Span

class AstThrowExpression(
    val throwKeyword: KeywordToken,
    val expression: Expression,
) : Expression {
    override val span: Span = throwKeyword.span .. expression.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        val throwableExpression = expression.bindTo(context)
        return BoundThrowExpression(
            throwableExpression.modifiedContext,
            throwableExpression,
            this,
        )
    }
}
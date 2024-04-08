package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundStringLiteralExpression
import compiler.lexer.OperatorToken
import compiler.lexer.StringLiteralContentToken

class StringLiteralExpression(
    val startingDelimiter: OperatorToken,
    val content: StringLiteralContentToken,
    val endingDelimiter: OperatorToken,
) :Expression {
    override val sourceLocation = startingDelimiter.sourceLocation .. endingDelimiter.sourceLocation

    override fun bindTo(context: ExecutionScopedCTContext): BoundStringLiteralExpression {
        return BoundStringLiteralExpression(context, this)
    }
}
package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundStringLiteralExpression
import compiler.lexer.OperatorToken
import compiler.lexer.SourceLocation
import compiler.lexer.StringLiteralContentToken

class StringLiteralExpression(
    val startingDelimiter: OperatorToken,
    val content: StringLiteralContentToken,
    val endingDelimiter: OperatorToken,
) : Expression<BoundStringLiteralExpression> {
    override val sourceLocation = SourceLocation(
        startingDelimiter.sourceLocation.file,
        startingDelimiter.sourceLocation.fromLineNumber,
        startingDelimiter.sourceLocation.fromColumnNumber,
        endingDelimiter.sourceLocation.toLineNumber,
        endingDelimiter.sourceLocation.toColumnNumber,
    )

    override fun bindTo(context: CTContext): BoundStringLiteralExpression {
        return BoundStringLiteralExpression(context, this)
    }
}
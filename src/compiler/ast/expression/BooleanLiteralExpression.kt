package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundBooleanLiteralExpression
import compiler.lexer.SourceLocation

class BooleanLiteralExpression(
    override val sourceLocation: SourceLocation,
    val value: Boolean
) : Expression<BoundBooleanLiteralExpression> {
    override fun bindTo(context: CTContext) = BoundBooleanLiteralExpression(context, this, value)
}
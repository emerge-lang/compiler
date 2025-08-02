package compiler.ast.expression

import compiler.ast.Expression
import compiler.ast.Expression.Companion.chain
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundArrayLiteralExpression
import compiler.lexer.OperatorToken

class ArrayLiteralExpression(
    val leftBracket: OperatorToken,
    val elements: List<Expression>,
    val rightBracket: OperatorToken,
) : Expression {
    override val span = leftBracket.span .. rightBracket.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundArrayLiteralExpression {
        return BoundArrayLiteralExpression(context, this, elements.chain(context).toList())
    }
}
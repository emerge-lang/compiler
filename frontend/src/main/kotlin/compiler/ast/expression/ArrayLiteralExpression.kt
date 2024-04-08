package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundArrayLiteralExpression
import compiler.binding.expression.BoundExpression
import compiler.lexer.OperatorToken

class ArrayLiteralExpression(
    val leftBracket: OperatorToken,
    val elements: List<Expression>,
    val rightBracket: OperatorToken,
) : Expression {
    override val sourceLocation = leftBracket.sourceLocation .. rightBracket.sourceLocation

    override fun bindTo(context: ExecutionScopedCTContext): BoundArrayLiteralExpression {
        var carryContext = context
        val boundElements = ArrayList<BoundExpression<*>>(elements.size)
        for (element in elements) {
            val boundElement = element.bindTo(carryContext)
            boundElements.add(boundElement)
            carryContext = boundElement.modifiedContext
        }

        return BoundArrayLiteralExpression(context, this, boundElements)
    }
}
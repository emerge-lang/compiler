package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundArrayLiteralExpression
import compiler.binding.expression.BoundExpression
import compiler.lexer.OperatorToken
import compiler.lexer.SourceLocation

class ArrayLiteralExpression(
    val leftBracket: OperatorToken,
    val elements: List<Expression>,
    val rightBracket: OperatorToken,
) : Expression {
    override val sourceLocation = SourceLocation(
        leftBracket.sourceLocation.file,
        leftBracket.sourceLocation.fromLineNumber,
        leftBracket.sourceLocation.fromColumnNumber,
        rightBracket.sourceLocation.toLineNumber,
        rightBracket.sourceLocation.toColumnNumber,
    )

    override fun bindTo(context: CTContext): BoundArrayLiteralExpression {
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
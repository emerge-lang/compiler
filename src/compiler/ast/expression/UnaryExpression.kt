package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundUnaryExpression
import compiler.lexer.Operator

class UnaryExpression(val operator: Operator, val valueExpression: Expression<*>): Expression<BoundUnaryExpression>
{
    override val sourceLocation = valueExpression.sourceLocation

    override fun bindTo(context: CTContext) = BoundUnaryExpression(
        context,
        this,
        valueExpression.bindTo(context)
    )
}
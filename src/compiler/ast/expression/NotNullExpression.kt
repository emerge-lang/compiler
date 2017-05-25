package compiler.ast.expression

import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundNotNullExpression
import compiler.lexer.OperatorToken

/** A not-null enforcement expression created by the !! operator */
class NotNullExpression(
    val nullableExpression: Expression<*>,
    val notNullOperator: OperatorToken
) : Expression<BoundNotNullExpression>, Executable<BoundNotNullExpression>
{
    override val sourceLocation = nullableExpression.sourceLocation

    override fun bindTo(context: CTContext) = BoundNotNullExpression(
        context,
        this,
        nullableExpression.bindTo(context)
    )
}
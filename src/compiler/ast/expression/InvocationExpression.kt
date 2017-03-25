package compiler.ast.expression

import compiler.ast.Executable
import compiler.binding.context.CTContext

class InvocationExpression(
    val receiverExpr: Expression,
    val parameterExprs: List<Expression>
) : Expression, Executable {
    override val sourceLocation = receiverExpr.sourceLocation

    override fun validate(context: CTContext) = super<Expression>.validate(context)
}
package compiler.ast.expression

import compiler.ast.Executable
import compiler.binding.BindingResult
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundInvocationExpression
import java.lang.UnsupportedOperationException

class InvocationExpression(
    val receiverExpr: Expression<*>,
    val parameterExprs: List<Expression<*>>
) : Expression<BoundInvocationExpression>, Executable<BoundInvocationExpression> {
    override val sourceLocation = receiverExpr.sourceLocation

    override fun bindTo(context: CTContext): BindingResult<BoundInvocationExpression> {
        throw UnsupportedOperationException()
    }
}
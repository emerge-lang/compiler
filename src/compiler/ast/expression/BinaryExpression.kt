package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundBinaryExpression
import compiler.lexer.OperatorToken

class BinaryExpression(
    val first: Expression<*>,
    val op: OperatorToken,
    val second: Expression<*>
) : Expression<BoundBinaryExpression> {
    override val sourceLocation = first.sourceLocation

    // simply rewrite to an invocation
    override fun bindTo(context: CTContext) = BoundBinaryExpression(
            context,
            this,
            first.bindTo(context),
            op.operator,
            second.bindTo(context)
    )
}
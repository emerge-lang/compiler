package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundBinaryExpression
import compiler.lexer.OperatorToken

class BinaryExpression(
        val leftHandSide: Expression<*>,
        val op: OperatorToken,
        val rightHandSide: Expression<*>
) : Expression<BoundBinaryExpression> {
    override val sourceLocation = leftHandSide.sourceLocation

    // simply rewrite to an invocation
    override fun bindTo(context: CTContext) = BoundBinaryExpression(
            context,
            this,
            leftHandSide.bindTo(context),
            op.operator,
            rightHandSide.bindTo(context)
    )
}
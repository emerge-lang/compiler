package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

/**
 * Models member access (`obj.member`). When evaluated like usual, attempts to access defined properties and extension
 * properties only.
 *
 * Member method invocation is handled by [InvocationExpression]. When its receiver expression is a [MemberAccessExpression],
 * it leftHandSide tries to resolve a member function with the [memberName] before evaluating this expression.
 *
 * @param accessOperatorToken must be either [Operator.DOT] or [Operator.SAFEDOT]
 */
class MemberAccessExpression(
        val valueExpression: Expression<*>,
        val accessOperatorToken: OperatorToken,
        val memberName: IdentifierToken
) : Expression<BoundMemberAccessExpression> {
    override val sourceLocation = valueExpression.sourceLocation

    override fun bindTo(context: CTContext): BoundMemberAccessExpression {
        return BoundMemberAccessExpression(
            context,
            this,
            valueExpression.bindTo(context),
            accessOperatorToken.operator == Operator.SAFEDOT,
            memberName.value
        )
    }
}
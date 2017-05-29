package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.lexer.IdentifierToken

/**
 * Models member access (`obj.member`). When evaluated like usual, attempts to access defined properties and extension
 * properties only.
 *
 * Member method invocation is handled by [InvocationExpression]. When its receiver expression is a [MemberAccessExpression],
 * it leftHandSide tries to resolve a member function with the [memberName] before evaluating this expression.
 */
class MemberAccessExpression(
    val valueExpression: Expression<*>,
    val memberName: IdentifierToken
) : Expression<BoundMemberAccessExpression> {
    override val sourceLocation = valueExpression.sourceLocation

    override fun bindTo(context: CTContext): BoundMemberAccessExpression {
        return BoundMemberAccessExpression(
            context,
            this,
            valueExpression.bindTo(context),
            memberName.value
        )
    }
}
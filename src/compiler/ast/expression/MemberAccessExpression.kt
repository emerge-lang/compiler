package compiler.ast.expression

import compiler.binding.BindingResult
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.lexer.IdentifierToken

/**
 * Models member access (`obj.member`). When evaluated like usual, attempts to access defined properties and extension
 * properties only.
 *
 * Member method invocation is handled by [InvocationExpression]. When its receiver expression is a [MemberAccessExpression],
 * it first tries to resolve a member function with the [memberName] before evaluating this expression.
 */
class MemberAccessExpression(
    val valueExpression: Expression<*>,
    val memberName: IdentifierToken
) : Expression<BoundMemberAccessExpression> {
    override val sourceLocation = valueExpression.sourceLocation

    override fun bindTo(context: CTContext): BindingResult<BoundMemberAccessExpression> {
        // TODO implement member variable lookup

        val valueExprBinding = valueExpression.bindTo(context)

        return BindingResult(
            BoundMemberAccessExpression(
                context,
                this,
                null,
                valueExprBinding.bound,
                memberName.value
            ),
            valueExprBinding.reportings
        )
    }
}
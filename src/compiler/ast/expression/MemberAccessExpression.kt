package compiler.ast.expression

import compiler.lexer.IdentifierToken

/**
 * Models member access (`obj.member`). When evaluated like usual, attempts to access defined properties and extension
 * properties only.
 *
 * Member method invocation is handled by [InvocationExpression]. When its receiver expression is a [MemberAccessExpression],
 * it first tries to resolve a member function with the [memberName] before evaluating this expression.
 */
class MemberAccessExpression(
    val valueExpression: Expression,
    val memberName: IdentifierToken
) : Expression {
    override val sourceLocation = valueExpression.sourceLocation
}
package compiler.parser

import compiler.ast.expression.AssignmentExpression
import compiler.ast.expression.Expression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.expression.NotNullExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.OperatorToken

/**
 * Given the expression itself, it returns a new expression that contains the information about the postfix.
 * E.g. matching the !! postfix results in a [NotNullExpressionPostfix] which in turn will wrap any given
 * [Expression] in a [NotNullExpression].
 */
interface ExpressionPostfix<out OutExprType: Expression<*>> {
    fun modify(expr: Expression<*>): OutExprType
}

class NotNullExpressionPostfix(
    /** The notnull operator for reference; whether the operator is actually [Operator.NOTNULL] is never checked.*/
    val notNullOperator: OperatorToken
) : ExpressionPostfix<NotNullExpression> {
    override fun modify(expr: Expression<*>) = NotNullExpression(expr, notNullOperator)
}

class InvocationExpressionPostfix(
    val parameterExpressions: List<Expression<*>>
) : ExpressionPostfix<InvocationExpression> {
    override fun modify(expr: Expression<*>) = InvocationExpression(expr, parameterExpressions)
}

class MemberAccessExpressionPostfix(
    /** must be either [Operator.DOT] or [Operator.SAFEDOT] */
    val accessOperatorToken: OperatorToken,
    val memberName: IdentifierToken
) : ExpressionPostfix<MemberAccessExpression> {
    override fun modify(expr: Expression<*>) = MemberAccessExpression(expr, accessOperatorToken, memberName)
}

class AssignmentExpressionPostfix(
    val assignmentOperator: OperatorToken,
    val value: Expression<*>,
) : ExpressionPostfix<AssignmentExpression> {
    override fun modify(expr: Expression<*>): AssignmentExpression {
        return AssignmentExpression(
            expr,
            assignmentOperator,
            value,
        )
    }
}
package compiler.ast

import compiler.ast.expression.Expression
import compiler.binding.BoundAssignmentStatement
import compiler.binding.context.CTContext
import compiler.lexer.OperatorToken

class AssignmentStatement(
    val targetExpression: Expression<*>,
    val assignmentOperatorToken: OperatorToken,
    val valueExpression: Expression<*>
) : Executable<BoundAssignmentStatement> {

    override val sourceLocation = targetExpression.sourceLocation

    override fun bindTo(context: CTContext) = BoundAssignmentStatement(
            context,
            this,
            targetExpression.bindTo(context),
            valueExpression.bindTo(context)
    )
}
package compiler.ast.expression

import compiler.lexer.SourceLocation

class InvocationExpression(
    val receiverExpr: Expression,
    val parameterExprs: List<Expression>
) : Expression {
    override val sourceLocation = receiverExpr.sourceLocation
}
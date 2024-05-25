package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIndexAccessExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Span

class AstIndexAccessExpression(
    val valueExpression: Expression,
    sBraceOpen: OperatorToken,
    val indexExpression: Expression,
    sBraceClose: OperatorToken,
) : Expression {
    override val span: Span = (sBraceOpen.span .. indexExpression.span) .. sBraceClose.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        val generatedSpan = span.deriveGenerated()
        val boundInvocation = InvocationExpression(
            MemberAccessExpression(
                valueExpression,
                OperatorToken(Operator.DOT, generatedSpan),
                IdentifierToken("get", generatedSpan),
            ),
            null,
            listOf(indexExpression),
            generatedSpan,
        ).bindTo(context)

        return BoundIndexAccessExpression(
            boundInvocation.context,
            this,
            boundInvocation,
        )
    }
}
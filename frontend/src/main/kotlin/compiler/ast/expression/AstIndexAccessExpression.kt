package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIndexAccessExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.GET_AT_INDEX_FN_NAME

class AstIndexAccessExpression(
    val valueExpression: Expression,
    sBraceOpen: OperatorToken,
    val indexExpression: Expression,
    sBraceClose: OperatorToken,
) : Expression {
    override val span: Span = (sBraceOpen.span .. indexExpression.span) .. sBraceClose.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        val boundInvocation = InvocationExpression(
            MemberAccessExpression(
                valueExpression,
                OperatorToken(Operator.DOT, span),
                IdentifierToken(GET_AT_INDEX_FN_NAME, span),
            ),
            null,
            listOf(indexExpression),
            span,
        ).bindTo(context)

        return BoundIndexAccessExpression(
            boundInvocation.context,
            this,
            boundInvocation,
        )
    }
}
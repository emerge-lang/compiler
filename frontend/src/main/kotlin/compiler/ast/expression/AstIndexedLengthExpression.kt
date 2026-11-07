package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIndexedLengthOutsideIndexExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

class AstIndexedLengthExpression(val token: OperatorToken) : Expression {
    override val span = token.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        val indexedValue = context.indexedValue
            ?: return BoundIndexedLengthOutsideIndexExpression(context, this)

        val generatedSpan = span.deriveGenerated()
        return MemberAccessExpression(
            indexedValue,
            OperatorToken(Operator.DOT, generatedSpan),
            IdentifierToken("size", generatedSpan),
        ).bindTo(context)
    }
}

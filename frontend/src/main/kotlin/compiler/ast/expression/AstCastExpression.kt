package compiler.ast.expression

import compiler.ast.Expression
import compiler.ast.type.TypeReference
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundCastExpression
import compiler.binding.expression.BoundExpression
import compiler.lexer.KeywordToken
import compiler.lexer.Span

class AstCastExpression(
    val value: Expression,
    val asToken: KeywordToken,
    val isSafe: Boolean,
    val toType: TypeReference,
) : Expression {
    override val span: Span = value.span .. (toType.span ?: asToken.span)

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        val boundValue = value.bindTo(context)
        return BoundCastExpression(
            boundValue.modifiedContext,
            this,
            boundValue,
            isSafe,
        )
    }
}
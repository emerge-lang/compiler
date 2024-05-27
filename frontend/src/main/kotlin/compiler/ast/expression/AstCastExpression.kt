package compiler.ast.expression

import compiler.ast.Expression
import compiler.ast.type.TypeReference
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundCastExpression
import compiler.binding.expression.BoundExpression
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Span

class AstCastExpression(
    val value: Expression,
    val operator: KeywordToken,
    val toType: TypeReference,
) : Expression {
    override val span: Span = value.span .. (toType.span ?: operator.span)

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        val boundValue = value.bindTo(context)
        return BoundCastExpression(
            boundValue.modifiedContext,
            this,
            boundValue,
            operator.keyword == Keyword.SAFE_AS,
        )
    }
}
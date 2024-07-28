package compiler.ast

import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundContinueExpression
import compiler.binding.expression.BoundExpression
import compiler.lexer.KeywordToken

class AstContinueExpression(
    val keyword: KeywordToken,
) : Expression {
    override val span = keyword.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        return BoundContinueExpression(context, this)
    }
}
package compiler.ast

import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundBreakExpression
import compiler.binding.expression.BoundExpression
import compiler.lexer.KeywordToken

class AstBreakExpression(
    val keyword: KeywordToken,
) : Expression {
    override val span = keyword.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        return BoundBreakExpression(context, this)
    }
}
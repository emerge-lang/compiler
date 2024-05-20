package compiler.ast

import compiler.binding.BoundStatement
import compiler.binding.BoundThrowStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.lexer.KeywordToken
import compiler.lexer.Span

class AstThrowStatement(
    val throwKeyword: KeywordToken,
    val expression: Expression,
) : Statement {
    override val span: Span = throwKeyword.span .. expression.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
        val throwableExpression = expression.bindTo(context)
        return BoundThrowStatement(
            throwableExpression.modifiedContext,
            throwableExpression,
            this,
        )
    }
}
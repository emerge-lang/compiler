package compiler.ast

import compiler.binding.BoundContinueStatement
import compiler.binding.BoundStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.lexer.KeywordToken

class AstContinueStatement(
    val keyword: KeywordToken,
) : Statement {
    override val span = keyword.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
        return BoundContinueStatement(context, this)
    }
}
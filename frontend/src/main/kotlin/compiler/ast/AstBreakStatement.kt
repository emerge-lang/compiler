package compiler.ast

import compiler.binding.BoundBreakStatement
import compiler.binding.BoundStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.lexer.KeywordToken

class AstBreakStatement(
    val keyword: KeywordToken,
) : Statement {
    override val span = keyword.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
        return BoundBreakStatement(context, this)
    }
}
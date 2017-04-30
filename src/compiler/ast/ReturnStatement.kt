package compiler.ast

import compiler.ast.expression.Expression
import compiler.binding.BoundReturnStatement
import compiler.binding.context.CTContext
import compiler.lexer.KeywordToken

class ReturnStatement(
    val returnKeyword: KeywordToken,
    val expression: Expression<*>
) : Executable<BoundReturnStatement> {
    override val sourceLocation = expression.sourceLocation

    override fun bindTo(context: CTContext) = BoundReturnStatement(context, this)
}
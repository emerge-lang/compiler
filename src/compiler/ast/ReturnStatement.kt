package compiler.ast

import compiler.ast.expression.Expression
import compiler.binding.BindingResult
import compiler.binding.BoundReturnStatement
import compiler.binding.context.CTContext
import compiler.lexer.KeywordToken

class ReturnStatement(
    val returnKeyword: KeywordToken,
    val expression: Expression<*>
) : Executable<BoundReturnStatement> {
    override val sourceLocation = expression.sourceLocation

    override fun bindTo(context: CTContext): BindingResult<BoundReturnStatement> {
        val expressionResult = expression.bindTo(context)

        return BindingResult(
            BoundReturnStatement(
                context,
                this,
                expressionResult.bound.type
            ),
            expressionResult.reportings
        )
    }
}
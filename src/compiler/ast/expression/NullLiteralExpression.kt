package compiler.ast.expression

import compiler.binding.BindingResult
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundNullLiteralExpression
import compiler.lexer.SourceLocation

/**
 * The null literal
 */
class NullLiteralExpression(
    override val sourceLocation: SourceLocation

) : Expression<BoundNullLiteralExpression> {
    override fun bindTo(context: CTContext)
        = BindingResult(
            BoundNullLiteralExpression(
                context,
                this
            ),
            emptySet()
        )
}

package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.IndexExecutionScopedCTContext
import compiler.binding.expression.BoundExpression

/**
 * Binds [indexExpression] such that `$` within it refers to the size of [indexedValue].
 */
class AstIndexExpressionScope(
    val indexExpression: Expression,
    val indexedValue: AstSharedValueExpression,
) : Expression {
    override val span get() = indexExpression.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        return indexExpression.bindTo(IndexExecutionScopedCTContext(context, indexedValue))
    }
}

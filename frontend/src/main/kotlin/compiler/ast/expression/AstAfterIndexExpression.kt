package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.AfterIndexExecutionScopedCTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression

/**
 * Binds [expression] such that `$` within it doesn't refer to [indexedValue], e.g. the value in `set a[i] = v`.
 */
class AstAfterIndexExpression(
    val expression: Expression,
    val indexedValue: AstSharedValueExpression,
) : Expression {
    override val span get() = expression.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        return expression.bindTo(AfterIndexExecutionScopedCTContext(context, indexedValue))
    }
}

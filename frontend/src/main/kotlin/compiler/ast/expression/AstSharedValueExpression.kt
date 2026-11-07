package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundSharedValueExpression
import compiler.binding.expression.BoundSharedValueReference

/**
 * Evaluates [value] once, but can be referred to more than once: the first [bindTo] binds [value], all later ones
 * refer to the result of that one evaluation. The first binding must also be evaluated first at runtime.
 */
class AstSharedValueExpression(val value: Expression) : Expression {
    override val span get() = value.span

    private var sharedValue: BoundSharedValueExpression? = null

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        sharedValue?.let { return BoundSharedValueReference(context, this, it) }
        return BoundSharedValueExpression(value.bindTo(context)).also { sharedValue = it }
    }
}

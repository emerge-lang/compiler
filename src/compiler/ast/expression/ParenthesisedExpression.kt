package compiler.ast.expression;

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.lexer.SourceLocation

/**
 * Wraps another [Expression] in order to influence evaluation order and operator precedence. The evidence of the
 * parenthesis is lost when binding this to a context: [.bindTo(CTContext)] delegates to [Expression.bindTo] of [nested].
 */
class ParenthesisedExpression<out NestedBoundType : BoundExpression<*>>(val nested: Expression<NestedBoundType>, override val sourceLocation: SourceLocation) : Expression<BoundExpression<*>> {
    override fun bindTo(context: CTContext): NestedBoundType {
        return nested.bindTo(context)
    }
}

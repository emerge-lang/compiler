package compiler.ast.expression;

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.lexer.SourceLocation
import compiler.parser.postproc.restructureWithRespectToOperatorPrecedence

/**
 * Wraps another [Expression] in order to influence evaluation order and operator precedence. The evidence of the
 * parenthesis is lost when binding this to a context: [.bindTo(CTContext)] delegates to [Expression.bindTo] of [nested].
 * By that time the tree structure of expressions is assumed to be correct (see [restructureWithRespectToOperatorPrecedence]).
 */
class ParenthesisedExpression<out NestedBoundType : BoundExpression<*>>(val nested: Expression<NestedBoundType>, override val sourceLocation: SourceLocation) : Expression<BoundExpression<*>> {
    override fun bindTo(context: CTContext): NestedBoundType {
        return nested.bindTo(context)
    }
}

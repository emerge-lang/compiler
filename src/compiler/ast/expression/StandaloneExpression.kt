package compiler.ast.expression

import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundStandaloneExpression

/**
 * A expression that may stand on its own within a [CodeChunk]; e.g. a expression that can have side-effects.
 */
class StandaloneExpression(
    val expression: Expression<*>
) : Expression<BoundStandaloneExpression>, Executable<BoundStandaloneExpression> {
    override val sourceLocation = expression.sourceLocation
    override fun bindTo(context: CTContext) = BoundStandaloneExpression(
        context,
        this,
        expression.bindTo(context)
    )
}
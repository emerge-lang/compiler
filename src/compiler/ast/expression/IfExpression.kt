package compiler.ast.expression

import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIfExpression
import compiler.lexer.SourceLocation

class IfExpression (
    override val sourceLocation: SourceLocation,
    val condition: Expression<BoundExpression<Expression<*>>>,
    val thenCode: Executable<*>,
    val elseCode: Executable<*>?
) : Expression<BoundIfExpression>, Executable<BoundIfExpression> {

    override fun bindTo(context: CTContext): BoundIfExpression {
        return BoundIfExpression(
            context,
            this,
            condition.bindTo(MutableCTContext(context)),
            thenCode?.bindTo(MutableCTContext(context)),
            elseCode?.bindTo(MutableCTContext(context))
        )
    }
}
package compiler.ast.expression

import compiler.ast.Executable
import compiler.binding.BindingResult
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundStandaloneExpression
import compiler.parser.Reporting

/**
 * A expression that may stand on its own within a [CodeChunk]; e.g. a expression that can have side-effects.
 * Currently this only applies to these Expressions:
 *
 * * [InvocationExpression]
 * * [NotNullExpression]
 */
class StandaloneExpression(
    val expr: Expression<*>
) : Expression<BoundStandaloneExpression>, Executable<BoundStandaloneExpression> {
    override val sourceLocation = expr.sourceLocation

    override fun bindTo(context: CTContext): BindingResult<BoundStandaloneExpression> {
        val reportings = mutableListOf<Reporting>()

        val subBR = expr.bindTo(context)
        reportings.addAll(subBR.reportings)

        val isOfStandaloneType = standaloneExpressionTypes.find { suitableTypeClass ->
            suitableTypeClass.isAssignableFrom(expr.javaClass)
        } != null

        if (!isOfStandaloneType) {
            reportings.add(Reporting.error("A $expr is not a statement.", sourceLocation))
            // TODO: if part of the chain is suitable, report the rest as superfluous with level WARNING instead of ERROR
        }

        return BindingResult(
            BoundStandaloneExpression(
                context,
                this,
                subBR.bound.type,
                subBR.bound
            ),
            reportings
        )
    }

    companion object {
        private val standaloneExpressionTypes: List<Class<out Expression<*>>> = listOf(
            InvocationExpression::class.java,
            NotNullExpression::class.java
        )
    }
}
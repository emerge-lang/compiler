package compiler.ast.expression

import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.parser.Reporting

/**
 * A expression that may stand on its own within a [CodeChunk]; e.g. a expression that can have side-effects.
 * Currently this only applies to these Expressions:
 *
 * * [InvocactionExpression]
 * * [NotNullExpression]
 */
class StandaloneExpression(
    val expr: Expression
) : Expression, Executable {
    override val sourceLocation = expr.sourceLocation

    override fun validate(context: CTContext): Collection<Reporting> {
        val subReportings = expr.validate(context)

        val isOfStandaloneType = standaloneExpressionTypes.find { suitableTypeClass ->
            suitableTypeClass.isAssignableFrom(expr.javaClass)
        } != null

        if (isOfStandaloneType) {
            return subReportings
        }
        else {
            val reportings = subReportings as? MutableList<Reporting> ?: subReportings.toMutableList()

            reportings.add(Reporting.error("A $expr is not a statement.", sourceLocation))
            // TODO: if part of the chain is suitable, report the rest as superfluous with level WARNING instead of ERROR

            return reportings
        }
    }

    companion object {
        private val standaloneExpressionTypes: List<Class<out Expression>> = listOf(
            InvocationExpression::class.java,
            NotNullExpression::class.java
        )
    }
}
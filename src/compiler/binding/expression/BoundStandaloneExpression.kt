package compiler.binding.expression

import compiler.ast.expression.StandaloneExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

/**
 * Currently this only applies to these Expressions:
 *
 * [BoundInvocationExpression]
 * [BoundNotNullExpression]
 *
 * These are listed in [Companion.standaloneExpressionTypes]; using an expression not listed in there will
 * generate warnings / errors.
 */
class BoundStandaloneExpression(
    override val context: CTContext,
    override val declaration: StandaloneExpression,
    val expression: BoundExpression<*>
) : BoundExpression<StandaloneExpression>, BoundExecutable<StandaloneExpression> {

    override val type: BaseTypeReference?
        get() = expression.type

    override val isReadonly: Boolean?
        get() = expression.isReadonly

    override fun semanticAnalysisPhase1(): Collection<Reporting> {

        val isOfStandaloneType = standaloneExpressionTypes.find { suitableTypeClass ->
            suitableTypeClass.isAssignableFrom(expression.javaClass)
        } != null

        val reportings = mutableListOf<Reporting>()
        if (!isOfStandaloneType) {
            reportings.add(Reporting.error("A $expression is not a statement.", declaration.sourceLocation))
            // TODO: if part of the chain is suitable, report the rest as superfluous with level WARNING instead of ERROR
        }

        reportings.addAll(expression.semanticAnalysisPhase1())

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return expression.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return super<BoundExpression>.semanticAnalysisPhase3()
    }

    companion object {
        private val standaloneExpressionTypes: List<Class<out BoundExpression<*>>> = listOf(
            BoundInvocationExpression::class.java,
            BoundNotNullExpression::class.java
        )
    }
}
package compiler.binding.expression

import compiler.ast.Expression
import compiler.ast.expression.AstIndexAccessExpression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.reportings.FunctionMissingModifierReporting.Companion.requireOperatorModifier
import compiler.reportings.Reporting

class BoundIndexAccessExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstIndexAccessExpression,
    private val hiddenInvocation: BoundInvocationExpression,
) : BoundExpression<Expression> by hiddenInvocation {
    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = hiddenInvocation.semanticAnalysisPhase2().toMutableList()

        requireOperatorModifier(
            hiddenInvocation,
            this,
            reportings,
        )

        return reportings
    }
}
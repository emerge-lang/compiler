package compiler.binding.expression

import compiler.ast.Expression
import compiler.ast.expression.AstIndexAccessExpression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.reportings.Diagnosis
import compiler.reportings.FunctionMissingModifierDiagnostic.Companion.requireOperatorModifier

class BoundIndexAccessExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstIndexAccessExpression,
    private val hiddenInvocation: BoundInvocationExpression,
) : BoundExpression<Expression> by hiddenInvocation {
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        hiddenInvocation.semanticAnalysisPhase2(diagnosis)

        requireOperatorModifier(
            hiddenInvocation,
            this,
            diagnosis,
        )
    }
}
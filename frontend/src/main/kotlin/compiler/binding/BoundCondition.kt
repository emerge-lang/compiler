package compiler.binding

import compiler.ast.Expression
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.isAssignableTo
import compiler.reportings.Reporting

class BoundCondition(
    val expression: BoundExpression<*>,
) : BoundExpression<Expression> by expression {
    override val type: BoundTypeReference get() = context.swCtx.bool.baseReference

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = expression.semanticAnalysisPhase2().toMutableList()

        if (expression.type?.isAssignableTo(context.swCtx.bool.baseReference) == false) {
            reportings.add(Reporting.conditionIsNotBoolean(expression))
        }

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = expression.semanticAnalysisPhase3().toMutableList()

        expression.findWritesBeyond(context)
            .map(Reporting::mutationInCondition)
            .forEach(reportings::add)

        return reportings
    }
}
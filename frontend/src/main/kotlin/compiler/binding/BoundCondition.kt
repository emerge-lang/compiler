package compiler.binding

import compiler.ast.Expression
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.isAssignableTo
import compiler.reportings.Diagnosis
import compiler.reportings.Reporting

class BoundCondition(
    val expression: BoundExpression<*>,
) : BoundExpression<Expression> by expression {
    override val type: BoundTypeReference get() = context.swCtx.bool.baseReference

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase2(diagnosis)

        if (expression.type?.isAssignableTo(context.swCtx.bool.baseReference) == false) {
            diagnosis.add(Reporting.conditionIsNotBoolean(expression))
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase3(diagnosis)

        expression.findWritesBeyond(context)
            .map(Reporting::mutationInCondition)
            .forEach(diagnosis::add)
    }
}
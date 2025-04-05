package compiler.binding

import compiler.ast.Expression
import compiler.ast.type.TypeMutability
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.IrrelevantValueUsage
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.isAssignableTo
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.conditionIsNotBoolean
import compiler.diagnostic.mutationInCondition

class BoundCondition(
    val expression: BoundExpression<*>,
) : BoundExpression<Expression> by expression {
    override val type: BoundTypeReference by lazy {
        context.swCtx.bool.baseReference.withMutability(TypeMutability.READONLY)
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase1(diagnosis)
        expression.markEvaluationResultUsed()
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase2(diagnosis)

        if (expression.type?.isAssignableTo(type) == false) {
            diagnosis.conditionIsNotBoolean(expression)
        }

        expression.setEvaluationResultUsage(IrrelevantValueUsage)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase3(diagnosis)

        expression.visitWritesBeyond(context) { impurity ->
            if (impurity.kind == PurityViolationDiagnostic.ActionKind.READ) {
                // reading in conditions is okay
                return@visitWritesBeyond
            }
            diagnosis.mutationInCondition(impurity)
        }
    }
}
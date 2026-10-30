package compiler.binding

import compiler.ast.AstAnnotation
import compiler.binding.expression.BoundExpression
import compiler.binding.impurity.ImpurityVisitor
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.purityViolation

class BoundAnnotation(
    val astNode: AstAnnotation,
    val expression: BoundExpression<*>,
) : SemanticallyAnalyzable {
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase1(diagnosis)
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase2(diagnosis)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        expression.semanticAnalysisPhase3(diagnosis)
        val visitor = ImpurityVisitor { impurity ->
            diagnosis.purityViolation(impurity, PurityViolationDiagnostic.SideEffectBoundary.Annotation(this@BoundAnnotation))
        }
        expression.visitReadsBeyond(expression.context, visitor)
        expression.visitWritesBeyond(expression.context, visitor)
    }
}
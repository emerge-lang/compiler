package compiler.binding

import compiler.InternalCompilerError
import compiler.ast.AssignmentStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundBinaryExpression
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIfExpression
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.expression.BoundLiteralExpression
import compiler.binding.expression.BoundNotNullExpression
import compiler.binding.expression.BoundUnaryExpression
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class BoundIllegalTargetAssignmentStatement(
    context: ExecutionScopedCTContext,
    declaration: AssignmentStatement,
    val targetExpression: BoundExpression<*>,
    toAssignExpression: BoundExpression<*>,
) : BoundAssignmentStatement(context, declaration, toAssignExpression) {
    override val targetThrowBehavior get() = targetExpression.throwBehavior
    override val targetReturnBehavior get() = targetExpression.returnBehavior

    override fun additionalSemanticAnalysisPhase1(diagnosis: Diagnosis) {
        targetExpression.semanticAnalysisPhase1(diagnosis)

        val targetDescription = when (targetExpression) {
            is BoundInvocationExpression -> "a function invocation"
            is BoundLiteralExpression -> "a literal"
            is BoundNotNullExpression -> "a not-null assertion"
            is BoundIfExpression -> "a conditional"
            is BoundBinaryExpression,
            is BoundUnaryExpression-> "an operator invocation"
            else -> "a ${targetExpression::class.simpleName!!.removePrefix("Bound").removeSuffix("Expression").lowercase()} expression"
        }

        diagnosis.add(
            Diagnostic.illegalAssignment("Cannot assign to $targetDescription", this)
        )
    }

    override fun assignmentTargetSemanticAnalysisPhase2(diagnosis: Diagnosis) {
        targetExpression.semanticAnalysisPhase2(diagnosis)
    }

    override val assignmentTargetType: BoundTypeReference? = null

    override fun additionalSemanticAnalysisPhase2(diagnosis: Diagnosis) = Unit

    override fun setTargetNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        targetExpression.setNothrow(boundary)
    }

    override fun additionalSemanticAnalysisPhase3(diagnosis: Diagnosis) = Unit

    override fun toBackendIrStatement(): IrExecutable {
        throw InternalCompilerError("This statement should never have passed semantic validation, cannot emit backend IR")
    }
}
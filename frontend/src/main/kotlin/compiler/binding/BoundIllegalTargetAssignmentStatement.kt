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
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class BoundIllegalTargetAssignmentStatement(
    context: ExecutionScopedCTContext,
    declaration: AssignmentStatement,
    val targetExpression: BoundExpression<*>,
    toAssignExpression: BoundExpression<*>,
) : BoundAssignmentStatement(context, declaration, toAssignExpression) {
    override val targetThrowBehavior get() = targetExpression.throwBehavior
    override val targetReturnBehavior get() = targetExpression.returnBehavior

    override fun additionalSemanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = targetExpression.semanticAnalysisPhase1().toMutableList()

        val targetDescription = when (targetExpression) {
            is BoundInvocationExpression -> "a function invocation"
            is BoundLiteralExpression -> "a literal"
            is BoundNotNullExpression -> "a not-null assertion"
            is BoundIfExpression -> "a conditional"
            is BoundBinaryExpression,
            is BoundUnaryExpression-> "an operator invocation"
            else -> "a ${targetExpression::class.simpleName!!.removePrefix("Bound").removeSuffix("Expression").lowercase()} expression"
        }

        reportings.add(
            Reporting.illegalAssignment("Cannot assign to $targetDescription", this)
        )

        return reportings
    }

    override fun assignmentTargetSemanticAnalysisPhase2(): Collection<Reporting> {
        return targetExpression.semanticAnalysisPhase2()
    }

    override val assignmentTargetType: BoundTypeReference? = null

    override fun additionalSemanticAnalysisPhase2(): Collection<Reporting> {
        return emptySet()
    }

    override fun setTargetNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        targetExpression.setNothrow(boundary)
    }

    override fun additionalSemanticAnalysisPhase3(): Collection<Reporting> {
        return emptySet()
    }

    override fun toBackendIrStatement(): IrExecutable {
        throw InternalCompilerError("This statement should never have passed semantic validation, cannot emit backend IR")
    }
}
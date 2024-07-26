package compiler.binding

import compiler.ast.AssignmentStatement
import compiler.ast.type.TypeMutability
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.PartialObjectInitialization
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundExpression.Companion.tryAsVariable
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

class BoundObjectMemberAssignmentStatement(
    context: ExecutionScopedCTContext,
    declaration: AssignmentStatement,
    val targetExpression: BoundMemberAccessExpression,
    toAssignExpression: BoundExpression<*>,
) : BoundAssignmentStatement(context, declaration, toAssignExpression) {
    init {
        targetExpression.usageContext = BoundMemberAccessExpression.UsageContext.WRITE
    }

    override val targetThrowBehavior get() = targetExpression.throwBehavior
    override val targetReturnBehavior get() = targetExpression.returnBehavior

    override fun additionalSemanticAnalysisPhase1(): Collection<Reporting> {
        return targetExpression.semanticAnalysisPhase1()
    }

    override fun assignmentTargetSemanticAnalysisPhase2(): Collection<Reporting> {
        return targetExpression.semanticAnalysisPhase2()
    }

    override val assignmentTargetType get() = targetExpression.type

    override fun setTargetNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        targetExpression.setNothrow(boundary)
    }

    override fun additionalSemanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        targetExpression.valueExpression.tryAsVariable()?.let { memberOwnerVariable ->
            targetExpression.member?.let { member ->
                val repetitionRelativeToMemberHolder = context.getRepetitionBehaviorRelativeTo(memberOwnerVariable.modifiedContext)

                initializationStateBefore = context.getEphemeralState(PartialObjectInitialization, memberOwnerVariable).getMemberInitializationState(member)
                if (initializationStateBefore == VariableInitialization.State.NOT_INITIALIZED || initializationStateBefore == VariableInitialization.State.MAYBE_INITIALIZED) {
                    _modifiedContext.trackSideEffect(
                        PartialObjectInitialization.Effect.WriteToMemberVariableEffect(memberOwnerVariable, member)
                    )
                }
                if (initializationStateBefore == VariableInitialization.State.MAYBE_INITIALIZED || repetitionRelativeToMemberHolder.mayRepeat) {
                    if (member.isReAssignable) {
                        _modifiedContext.trackSideEffect(PartialObjectInitialization.Effect.WriteToMemberVariableEffect(memberOwnerVariable, member))
                    } else {
                        reportings.add(Reporting.illegalAssignment("Member variable ${member.name} may already have been initialized, cannot assign a value again", this))
                    }
                }
                if (initializationStateBefore == VariableInitialization.State.INITIALIZED) {
                    if (!member.isReAssignable) {
                        reportings.add(Reporting.illegalAssignment("Member variable ${member.name} is already initialized, cannot re-assign", this))
                    }
                }
            }
        }

        return reportings
    }

    private var initializationStateBefore: VariableInitialization.State? = null

    override fun additionalSemanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        reportings.addAll(targetExpression.semanticAnalysisPhase3())

        targetExpression.valueExpression.type?.let { memberOwnerType ->
            if (!memberOwnerType.mutability.isMutable) {
                reportings += Reporting.valueNotAssignable(
                    memberOwnerType.withMutability(TypeMutability.MUTABLE),
                    memberOwnerType,
                    "Cannot mutate a value of type $memberOwnerType",
                    targetExpression.valueExpression.declaration.span,
                )
            }
        }
        targetExpression.type?.let { targetType ->
            toAssignExpression.type?.evaluateAssignabilityTo(targetType, toAssignExpression.declaration.span)
                ?.let(reportings::add)
        }

        return reportings
    }

    override fun toBackendIrStatement(): IrExecutable {
        val dropPreviousReferenceCode: IrCodeChunk?
        if (initializationStateBefore == VariableInitialization.State.NOT_INITIALIZED) {
            // this is the first assignment, no need to drop a previous reference
            dropPreviousReferenceCode = null
        } else {
            var previousType = targetExpression.type!!.toBackendIr()
            if (initializationStateBefore == VariableInitialization.State.MAYBE_INITIALIZED) {
                // forces a null-check on the reference drop, which prevents a nullpointer deref for an empty object
                previousType = previousType.nullable()
            }
            val previousTemporary = IrCreateTemporaryValueImpl(targetExpression.toBackendIrExpression(), previousType)
            dropPreviousReferenceCode = IrCodeChunkImpl(listOf(
                previousTemporary,
                IrDropStrongReferenceStatementImpl(previousTemporary),
            ))
        }

        val baseTemporary = IrCreateTemporaryValueImpl(targetExpression.valueExpression.toBackendIrExpression())
        val baseTemporaryRefIncrement = IrCreateStrongReferenceStatementImpl(baseTemporary)
            .takeUnless { targetExpression.valueExpression.isEvaluationResultReferenceCounted }
            .takeUnless { targetExpression.valueExpression.isEvaluationResultAnchored }
        val toAssignTemporary = IrCreateTemporaryValueImpl(toAssignExpression.toBackendIrExpression())
        val toAssignRefIncrement = IrCreateStrongReferenceStatementImpl(toAssignTemporary)
            .takeUnless { toAssignExpression.isEvaluationResultReferenceCounted }

        return IrCodeChunkImpl(listOfNotNull(
            baseTemporary,
            baseTemporaryRefIncrement,
            toAssignTemporary,
            toAssignRefIncrement,
            dropPreviousReferenceCode,
            IrAssignmentStatementImpl(
                IrAssignmentStatementTargetClassMemberVariableImpl(
                    targetExpression.member!!.toBackendIr(),
                    IrTemporaryValueReferenceImpl(baseTemporary),
                ),
                IrTemporaryValueReferenceImpl(toAssignTemporary),
            ),
            IrDropStrongReferenceStatementImpl(baseTemporary)
                .takeUnless { targetExpression.valueExpression.isEvaluationResultAnchored },
        ))
    }
}

internal class IrAssignmentStatementTargetClassMemberVariableImpl(
    override val memberVariable: IrClass.MemberVariable,
    override val objectValue: IrTemporaryValueReference,
) : IrAssignmentStatement.Target.ClassMemberVariable
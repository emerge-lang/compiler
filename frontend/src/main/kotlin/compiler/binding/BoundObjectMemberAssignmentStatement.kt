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
import kotlin.properties.Delegates

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

    private var accessBaseVariable: BoundVariable? = null

    override fun additionalSemanticAnalysisPhase2(): Collection<Reporting> {
        accessBaseVariable = targetExpression.valueExpression.tryAsVariable()

        accessBaseVariable?.let { baseVar ->
            targetExpression.member?.let { member ->
                _modifiedContext.trackSideEffect(
                    PartialObjectInitialization.Effect.WriteToMemberVariableEffect(baseVar, member)
                )
            }
        }

        return emptySet()
    }

    override fun setTargetNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        targetExpression.setNothrow(boundary)
    }

    private var memberIsPotentiallyUninitialized by Delegates.notNull<Boolean>()

    override fun additionalSemanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        reportings.addAll(targetExpression.semanticAnalysisPhase3())

        val memberInitializationStateBeforeAssignment = accessBaseVariable?.let { baseVar ->
            targetExpression.member?.let { member ->
                context.getEphemeralState(PartialObjectInitialization, baseVar).getMemberInitializationState(member)
            }
        } ?: VariableInitialization.State.MAYBE_INITIALIZED
        memberIsPotentiallyUninitialized = memberInitializationStateBeforeAssignment != VariableInitialization.State.INITIALIZED

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

        if (!memberIsPotentiallyUninitialized && targetExpression.member?.isReAssignable == false) {
            reportings.add(Reporting.illegalAssignment("Member variable ${targetExpression.member!!.name} cannot be re-assigned", this))
        }

        nothrowBoundary?.let { nothrowBoundary ->
            if (memberInitializationStateBeforeAssignment != VariableInitialization.State.NOT_INITIALIZED) {
                if (targetExpression.type?.destructorThrowBehavior != SideEffectPrediction.NEVER) {
                    reportings.add(Reporting.droppingReferenceToObjectWithThrowingConstructor(this, nothrowBoundary))
                }
            }
        }

        return reportings
    }

    override fun toBackendIrStatement(): IrExecutable {
        val dropPreviousReferenceCode: IrCodeChunk
        if (targetExpression.member!!.isReAssignable) {
            var previousType = targetExpression.type!!.toBackendIr()
            if (memberIsPotentiallyUninitialized) {
                // forces a null-check on the reference drop, which prevents a nullpointer deref for an empty object
                previousType = previousType.nullable()
            }
            val previousTemporary = IrCreateTemporaryValueImpl(targetExpression.toBackendIrExpression(), previousType)
            dropPreviousReferenceCode = IrCodeChunkImpl(listOf(
                previousTemporary,
                IrDropStrongReferenceStatementImpl(previousTemporary),
            ))
        } else {
            check(memberIsPotentiallyUninitialized) { "multiple assignments to a non-reassignable target" }
            // this is the first and only assignment, no need to drop a previous reference
            dropPreviousReferenceCode = IrCodeChunkImpl(emptyList())
        }

        val baseTemporary = IrCreateTemporaryValueImpl(targetExpression.valueExpression.toBackendIrExpression())
        val baseTemporaryRefIncrement = IrCreateStrongReferenceStatementImpl(baseTemporary).takeUnless { targetExpression.valueExpression.isEvaluationResultReferenceCounted }
        val toAssignTemporary = IrCreateTemporaryValueImpl(toAssignExpression.toBackendIrExpression())
        val toAssignTemporaryRefIncrement = IrCreateStrongReferenceStatementImpl(toAssignTemporary).takeUnless { toAssignExpression.isEvaluationResultReferenceCounted }

        return IrCodeChunkImpl(listOfNotNull(
            dropPreviousReferenceCode,
            baseTemporary,
            baseTemporaryRefIncrement,
            toAssignTemporary,
            toAssignTemporaryRefIncrement,
            IrAssignmentStatementImpl(
                IrAssignmentStatementTargetClassMemberVariableImpl(
                    targetExpression.member!!.toBackendIr(),
                    IrTemporaryValueReferenceImpl(baseTemporary),
                ),
                IrTemporaryValueReferenceImpl(toAssignTemporary),
            ),
            IrDropStrongReferenceStatementImpl(baseTemporary),
        ))
    }
}

internal class IrAssignmentStatementTargetClassMemberVariableImpl(
    override val memberVariable: IrClass.MemberVariable,
    override val objectValue: IrTemporaryValueReference,
) : IrAssignmentStatement.Target.ClassMemberVariable
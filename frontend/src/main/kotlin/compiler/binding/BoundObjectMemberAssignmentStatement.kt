package compiler.binding

import compiler.ast.AssignmentStatement
import compiler.ast.VariableOwnership
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.TypeMutability
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.PartialObjectInitialization
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundExpression.Companion.tryAsVariable
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.expression.CandidateFunctionFilter
import compiler.binding.expression.CreateReferenceValueUsage
import compiler.binding.expression.IrClassFieldAccessExpressionImpl
import compiler.binding.expression.ValueUsage
import compiler.binding.impurity.Impurity
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.impurity.ReassignmentBeyondBoundary
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.diagnostic.AmbiguousInvocationDiagnostic
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnosis.Companion.doWithTransformedFindings
import compiler.diagnostic.FunctionMissingModifierDiagnostic
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.UnresolvableFunctionOverloadDiagnostic
import compiler.diagnostic.ambiguousMemberVariableWrite
import compiler.diagnostic.illegalAssignment
import compiler.diagnostic.superfluousSafeObjectTraversal
import compiler.diagnostic.unsafeObjectTraversal
import compiler.diagnostic.valueNotAssignable
import compiler.lexer.Keyword
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

class BoundObjectMemberAssignmentStatement(
    context: ExecutionScopedCTContext,
    declaration: AssignmentStatement<MemberAccessExpression>,
    val targetObjectExpression: BoundExpression<*>,
    val isNullSafeAccess: Boolean,
    val memberName: String,
    toAssignExpression: BoundExpression<*>,
) : BoundAssignmentStatement<MemberAccessExpression>(context, declaration, toAssignExpression) {
    private var physicalMember: BoundBaseTypeMemberVariable? = null
    private var setterInvocation: BoundInvocationExpression = InvocationExpression(
        declaration.targetExpression,
        null,
        listOf(declaration.valueExpression),
        declaration.span,
    ).bindTo(context)

    override val targetThrowBehavior get() = if (physicalMember != null) SideEffectPrediction.NEVER else setterInvocation.throwBehavior
    override val targetReturnBehavior get() = if (physicalMember != null) SideEffectPrediction.NEVER else setterInvocation.returnBehavior

    override fun additionalSemanticAnalysisPhase1(diagnosis: Diagnosis) {
        targetObjectExpression.semanticAnalysisPhase1(diagnosis)
        setterInvocation.semanticAnalysisPhase1(diagnosis)
    }

    override fun assignmentTargetSemanticAnalysisPhase2(diagnosis: Diagnosis) {
        targetObjectExpression.semanticAnalysisPhase2(diagnosis)
        val baseType = targetObjectExpression.type ?: return
        if (baseType.isNullable && !isNullSafeAccess) {
            diagnosis.unsafeObjectTraversal(targetObjectExpression, declaration.targetExpression.accessOperatorToken)
        } else if (!baseType.isNullable && isNullSafeAccess) {
            diagnosis.superfluousSafeObjectTraversal(targetObjectExpression, declaration.targetExpression.accessOperatorToken)
        }

        physicalMember = baseType.findMemberVariable(memberName)
    }

    override val assignmentTargetType get() = if (physicalMember != null) {
        physicalMember!!.type
    } else {
        setterInvocation.functionToInvoke?.parameterTypes?.getOrNull(1)
    }

    override val assignedValueUsage: ValueUsage get() = CreateReferenceValueUsage(
        assignmentTargetType,
        declaration.targetExpression.memberName.span,
        VariableOwnership.CAPTURED,
    )

    override fun setTargetNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        targetObjectExpression.setNothrow(boundary)
    }

    override fun additionalSemanticAnalysisPhase2(diagnosis: Diagnosis) {
        setterInvocation.candidateFilter = SetterFilter()
        val availableSetters = mutableSetOf<BoundFunction>()
        diagnosis.doWithTransformedFindings(setterInvocation::semanticAnalysisPhase2) { findings ->
            findings.mapNotNull { finding ->
                if (finding is AmbiguousInvocationDiagnostic && finding.invocation === setterInvocation.declaration) {
                    availableSetters.addAll(finding.candidates)
                    return@mapNotNull null
                }

                if (finding is UnresolvableFunctionOverloadDiagnostic && finding.functionNameReference.span == declaration.targetExpression.memberName.span) {
                    availableSetters.clear()
                    return@mapNotNull null
                }

                return@mapNotNull if (physicalMember == null) {
                    finding
                } else {
                    null
                }
            }
        }
        setterInvocation.functionToInvoke?.let(availableSetters::add)

        physicalMember?.let { member ->
            targetObjectExpression.tryAsVariable()?.let { memberOwnerVariable ->
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
                        diagnosis.illegalAssignment("Member variable ${member.name} may already have been initialized, cannot assign a value again", this@BoundObjectMemberAssignmentStatement)
                    }
                }
                if (initializationStateBefore == VariableInitialization.State.INITIALIZED) {
                    if (!member.isReAssignable) {
                        diagnosis.illegalAssignment("Member variable ${member.name} is already initialized, cannot re-assign", this@BoundObjectMemberAssignmentStatement)
                    }
                }
            }

            member.validateAccessFrom(declaration.span, diagnosis)
        }

        if (availableSetters.size > 1 || (availableSetters.isNotEmpty() && physicalMember != null)) {
            diagnosis.ambiguousMemberVariableWrite(this, physicalMember, availableSetters)
        }
    }

    private var initializationStateBefore: VariableInitialization.State? = null

    override fun additionalSemanticAnalysisPhase3(diagnosis: Diagnosis) {
        targetObjectExpression.semanticAnalysisPhase3(diagnosis)

        targetObjectExpression.type?.let { memberOwnerType ->
            if (!memberOwnerType.mutability.isMutable) {
                diagnosis.valueNotAssignable(
                    memberOwnerType.withMutability(TypeMutability.MUTABLE),
                    memberOwnerType,
                    "Cannot mutate a value of type $memberOwnerType",
                    targetObjectExpression.declaration.span,
                )
            }
        }

        if (physicalMember == null) {
            setterInvocation.semanticAnalysisPhase3(diagnosis)
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        super.visitReadsBeyond(boundary, visitor)
        targetObjectExpression.visitReadsBeyond(boundary, visitor)
        // the member access can't possibly read more than the targetObjectExpression already does
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        super.visitWritesBeyond(boundary, visitor)
        targetObjectExpression.visitWritesBeyond(boundary, visitor)
        var targetReadsBeyondBoundary = false
        targetObjectExpression.visitReadsBeyond(boundary) { impurity ->
            if (impurity.kind == Impurity.ActionKind.READ) {
                targetReadsBeyondBoundary = true
            }
        }
        if (targetReadsBeyondBoundary) {
            // TODO: does this need more detail? information from the reading impurity is dropped
            visitor.visit(ReassignmentBeyondBoundary.MemberVariable(memberName, targetObjectExpression.declaration.span .. declaration.valueExpression.span))
        }
    }

    private inner class SetterFilter : CandidateFunctionFilter {
        override fun inspect(candidate: BoundFunction): CandidateFunctionFilter.Result {
            return if (candidate.attributes.firstAccessorAttribute?.kind == AccessorKind.Write) {
                CandidateFunctionFilter.Result.Applicable
            } else {
                CandidateFunctionFilter.Result.Inapplicable(FunctionMissingModifierDiagnostic(
                    candidate,
                    this@BoundObjectMemberAssignmentStatement.declaration,
                    Keyword.SET.text,
                ))
            }
        }
    }

    override fun toBackendIrStatement(): IrExecutable {
        val member = physicalMember ?: return setterInvocation.toBackendIrStatement()

        val baseTemporary = IrCreateTemporaryValueImpl(targetObjectExpression.toBackendIrExpression())

        val dropPreviousReferenceCode: IrCodeChunk?
        if (initializationStateBefore == VariableInitialization.State.NOT_INITIALIZED) {
            // this is the first assignment, no need to drop a previous reference
            dropPreviousReferenceCode = null
        } else {
            var previousType = member.type!!.toBackendIr()
            if (initializationStateBefore == VariableInitialization.State.MAYBE_INITIALIZED) {
                // forces a null-check on the reference drop, which prevents a nullpointer deref for an empty object
                previousType = previousType.nullable()
            }
            val previousTemporary = IrCreateTemporaryValueImpl(
                IrClassFieldAccessExpressionImpl(
                    IrTemporaryValueReferenceImpl(baseTemporary),
                    member.field.toBackendIr(),
                    previousType,
                ),
                previousType
            )
            dropPreviousReferenceCode = IrCodeChunkImpl(listOf(
                previousTemporary,
                IrDropStrongReferenceStatementImpl(previousTemporary),
            ))
        }

        val baseTemporaryRefIncrement = IrCreateStrongReferenceStatementImpl(baseTemporary)
            .takeUnless { targetObjectExpression.isEvaluationResultReferenceCounted }
            .takeUnless { targetObjectExpression.isEvaluationResultAnchored }
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
                IrAssignmentStatementTargetClassFieldImpl(
                    member.field.toBackendIr(),
                    IrTemporaryValueReferenceImpl(baseTemporary),
                ),
                IrTemporaryValueReferenceImpl(toAssignTemporary),
            ),
            IrDropStrongReferenceStatementImpl(baseTemporary)
                .takeUnless { targetObjectExpression.isEvaluationResultAnchored },
        ))
    }
}

internal class IrAssignmentStatementTargetClassFieldImpl(
    override val field: IrClass.Field,
    override val objectValue: IrTemporaryValueReference,
) : IrAssignmentStatement.Target.ClassField
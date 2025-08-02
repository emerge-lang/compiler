package compiler.binding.expression

import compiler.ast.expression.BinaryExpression
import compiler.ast.type.TypeReference
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrIsNullExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.nullCheckOnNonNullableValue
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

class BoundNullCoalescingExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: BinaryExpression,
    val nullableExpression: BoundExpression<*>,
    val alternativeExpression: BoundExpression<*>,
) : BoundExpression<BinaryExpression> {
    override val modifiedContext: ExecutionScopedCTContext = SingleBranchJoinExecutionScopedCTContext(nullableExpression.modifiedContext, alternativeExpression.modifiedContext)

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        nullableExpression.setNothrow(boundary)
        alternativeExpression.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        nullableExpression.semanticAnalysisPhase1(diagnosis)
        alternativeExpression.semanticAnalysisPhase1(diagnosis)

        // it will be null-checked in any case
        nullableExpression.markEvaluationResultUsed()
    }

    private var evaluationResultUsed = false

    override fun markEvaluationResultUsed() {
        evaluationResultUsed = true

        // this one gets dropped, though, if the entire coalesce-op is not used
        alternativeExpression.markEvaluationResultUsed()
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        nullableExpression.setExpectedEvaluationResultType(type.withCombinedNullability(TypeReference.Nullability.NULLABLE), diagnosis)
        alternativeExpression.setExpectedEvaluationResultType(type, diagnosis)
    }

    override var type: BoundTypeReference? = null
        private set

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        nullableExpression.semanticAnalysisPhase2(diagnosis)
        alternativeExpression.semanticAnalysisPhase2(diagnosis)

        val notNullableType = nullableExpression.type?.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
            ?: context.swCtx.getBottomType(declaration.operator.token.span)
        val alternateType = alternativeExpression.type
        this.type = alternateType?.closestCommonSupertypeWith(notNullableType) ?: notNullableType

        if (nullableExpression.type?.isNullable == false) {
            diagnosis.nullCheckOnNonNullableValue(nullableExpression)
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        nullableExpression.setExpectedReturnType(type, diagnosis)
        alternativeExpression.setExpectedReturnType(type, diagnosis)
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        nullableExpression.setEvaluationResultUsage(valueUsage)
        alternativeExpression.setEvaluationResultUsage(valueUsage)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        nullableExpression.semanticAnalysisPhase3(diagnosis)
        alternativeExpression.semanticAnalysisPhase3(diagnosis)
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        nullableExpression.visitReadsBeyond(boundary, visitor)
        alternativeExpression.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        nullableExpression.visitWritesBeyond(boundary, visitor)
        alternativeExpression.visitWritesBeyond(boundary, visitor)
    }

    override val isEvaluationResultReferenceCounted: Boolean
        get() = nullableExpression.isEvaluationResultReferenceCounted || alternativeExpression.isEvaluationResultReferenceCounted

    override val isEvaluationResultAnchored: Boolean
        get() = nullableExpression.isEvaluationResultAnchored && alternativeExpression.isEvaluationResultAnchored

    override val isCompileTimeConstant: Boolean
        get() = nullableExpression.isCompileTimeConstant && alternativeExpression.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        val nullableValueTemporary = IrCreateTemporaryValueImpl(nullableExpression.toBackendIrExpression())
        val isNullTemporary = IrCreateTemporaryValueImpl(IrIsNullExpressionImpl(
            IrTemporaryValueReferenceImpl(nullableValueTemporary),
            context.swCtx,
        ))

        val alternateValueTemporary = IrCreateTemporaryValueImpl(alternativeExpression.toBackendIrExpression())

        val conditionalResultTemporary = IrCreateTemporaryValueImpl(IrIfExpressionImpl(
            IrTemporaryValueReferenceImpl(isNullTemporary),
            IrImplicitEvaluationExpressionImpl(
                IrCodeChunkImpl(listOfNotNull(
                    IrUpdateSourceLocationStatementImpl(alternativeExpression.declaration.span),
                    // nullableTemporary is null, no need to drop a reference count
                    alternateValueTemporary,
                    IrCreateStrongReferenceStatementImpl(alternateValueTemporary)
                        .takeIf { this.isEvaluationResultReferenceCounted && !alternativeExpression.isEvaluationResultReferenceCounted }
                )),
                IrTemporaryValueReferenceImpl(alternateValueTemporary)
            ),
            IrImplicitEvaluationExpressionImpl(
                IrCodeChunkImpl(listOfNotNull(
                    IrCreateStrongReferenceStatementImpl(nullableValueTemporary)
                        .takeIf { this.isEvaluationResultReferenceCounted && !nullableExpression.isEvaluationResultReferenceCounted },
                )),
                IrTemporaryValueReferenceImpl(nullableValueTemporary),
            ),
            type!!.toBackendIr(),
        ))

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOfNotNull(
                IrUpdateSourceLocationStatementImpl(nullableExpression.declaration.span),
                nullableValueTemporary,
                isNullTemporary,
                conditionalResultTemporary,
                IrDropStrongReferenceStatementImpl(conditionalResultTemporary)
                    .takeIf { !this.evaluationResultUsed && this.isEvaluationResultReferenceCounted },
            )),
            IrTemporaryValueReferenceImpl(conditionalResultTemporary),
        )
    }
}
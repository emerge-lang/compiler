package compiler.binding.expression

import compiler.ast.expression.BinaryExpression
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundStatement
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SideEffectPrediction
import compiler.binding.SideEffectPrediction.Companion.combineBranch
import compiler.binding.SideEffectPrediction.Companion.combineSequentialExecution
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrIdentityComparisonExpressionImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.binding.type.BoundTypeReference
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

class BoundNullCoalescingExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: BinaryExpression,
    val nullableExpression: BoundExpression<*>,
    val alternativeExpression: BoundExpression<*>,
) : BoundExpression<BinaryExpression> {
    override val throwBehavior: SideEffectPrediction? get()= nullableExpression.throwBehavior.combineSequentialExecution(
        // never because if nullableExpression is not null, no code gets executed
        alternativeExpression.throwBehavior.combineBranch(SideEffectPrediction.NEVER)
    )

    override val returnBehavior: SideEffectPrediction? get() = nullableExpression.returnBehavior.combineSequentialExecution(
        alternativeExpression.returnBehavior.combineBranch(SideEffectPrediction.NEVER)
    )

    override val modifiedContext: ExecutionScopedCTContext = SingleBranchJoinExecutionScopedCTContext(nullableExpression.modifiedContext, alternativeExpression.modifiedContext)

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        nullableExpression.setNothrow(boundary)
        alternativeExpression.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(nullableExpression.semanticAnalysisPhase1())
        reportings.addAll(alternativeExpression.semanticAnalysisPhase1())

        // it will be null-checked in any case
        nullableExpression.markEvaluationResultUsed()

        return reportings
    }

    private var evaluationResultUsed = false

    override fun markEvaluationResultUsed() {
        evaluationResultUsed = true

        // this one gets dropped, though, if the entire coalesce-op is not used
        alternativeExpression.markEvaluationResultUsed()
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        nullableExpression.setExpectedEvaluationResultType(type)
        alternativeExpression.setExpectedEvaluationResultType(type)
    }

    override var type: BoundTypeReference? = null
        private set

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(nullableExpression.semanticAnalysisPhase2())
        reportings.addAll(alternativeExpression.semanticAnalysisPhase2())

        val notNullableType = nullableExpression.type?.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
            ?: context.swCtx.nothing.baseReference
        val alternateType = alternativeExpression.type
        this.type = alternateType?.closestCommonSupertypeWith(notNullableType) ?: notNullableType

        if (nullableExpression.type?.isNullable == false) {
            reportings.add(Reporting.nullCheckOnNonNullableValue(nullableExpression))
        }

        return reportings
    }

    override fun markEvaluationResultCaptured(withMutability: TypeMutability) {
        nullableExpression.markEvaluationResultCaptured(withMutability)
        alternativeExpression.markEvaluationResultCaptured(withMutability)
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        nullableExpression.setExpectedReturnType(type)
        alternativeExpression.setExpectedReturnType(type)
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(nullableExpression.semanticAnalysisPhase3())
        reportings.addAll(alternativeExpression.semanticAnalysisPhase3())
        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return nullableExpression.findReadsBeyond(boundary) + alternativeExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        return nullableExpression.findWritesBeyond(boundary) + alternativeExpression.findWritesBeyond(boundary)
    }

    override val isEvaluationResultReferenceCounted: Boolean
        get() = nullableExpression.isEvaluationResultReferenceCounted || alternativeExpression.isEvaluationResultReferenceCounted

    override val isCompileTimeConstant: Boolean
        get() = nullableExpression.isCompileTimeConstant && alternativeExpression.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        val nullableValueTemporary = IrCreateTemporaryValueImpl(nullableExpression.toBackendIrExpression())
        val nullLiteralTemporary = IrCreateTemporaryValueImpl(IrNullLiteralExpressionImpl(nullableExpression.type!!.toBackendIr().asNullable()))
        val isNullTemporary = IrCreateTemporaryValueImpl(IrIdentityComparisonExpressionImpl(
            IrTemporaryValueReferenceImpl(nullableValueTemporary),
            IrTemporaryValueReferenceImpl(nullLiteralTemporary),
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
                nullLiteralTemporary,
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
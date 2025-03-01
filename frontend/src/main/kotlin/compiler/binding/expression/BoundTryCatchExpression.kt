package compiler.binding.expression

import compiler.ast.expression.AstTryCatchExpression
import compiler.ast.type.TypeMutability
import compiler.binding.BoundCodeChunk
import compiler.binding.ImpurityVisitor
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.SideEffectPrediction.Companion.combineBranch
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTryCatchExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

class BoundTryCatchExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstTryCatchExpression,
    val fallibleCode: BoundCodeChunk,
    val catchBlock: BoundCatchBlockExpression,
) : BoundExpression<AstTryCatchExpression> {
    override val throwBehavior get() = fallibleCode.throwBehavior.combineBranch(catchBlock.throwBehavior)
    override val returnBehavior get() = fallibleCode.returnBehavior.combineBranch(catchBlock.returnBehavior)
    override val modifiedContext = context

    override val isEvaluationResultReferenceCounted = fallibleCode.isEvaluationResultReferenceCounted || catchBlock.isEvaluationResultReferenceCounted
    override val isEvaluationResultAnchored = fallibleCode.isEvaluationResultAnchored && catchBlock.isEvaluationResultAnchored

    override val isCompileTimeConstant: Boolean get() = when (fallibleCode.throwBehavior) {
        SideEffectPrediction.NEVER -> fallibleCode.isCompileTimeConstant
        SideEffectPrediction.GUARANTEED -> catchBlock.isCompileTimeConstant
        else -> false
    }

    override val type: BoundTypeReference? get() {
        val fallibleType = fallibleCode.type
        val catchType = catchBlock.type

        if (fallibleType == null || catchType == null) {
            return null
        }

        return fallibleType.closestCommonSupertypeWith(catchType)
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            fallibleCode.semanticAnalysisPhase1(diagnosis)
            catchBlock.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        fallibleCode.setExpectedEvaluationResultType(type, diagnosis)
        catchBlock.setExpectedEvaluationResultType(type, diagnosis)
    }

    override fun markEvaluationResultUsed() {
        fallibleCode.markEvaluationResultUsed()
        catchBlock.markEvaluationResultUsed()
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            fallibleCode.semanticAnalysisPhase2(diagnosis)
            catchBlock.semanticAnalysisPhase2(diagnosis)
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        fallibleCode.setExpectedReturnType(type, diagnosis)
        catchBlock.setExpectedReturnType(type, diagnosis)
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        // note that even a catch-all cannot make code nothrow! Errors fall through
        fallibleCode.setNothrow(boundary)
        catchBlock.setNothrow(boundary)
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor, diagnosis: Diagnosis) {
        fallibleCode.visitReadsBeyond(boundary, visitor, diagnosis)
        catchBlock.visitReadsBeyond(boundary, visitor, diagnosis)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor, diagnosis: Diagnosis) {
        fallibleCode.visitWritesBeyond(boundary, visitor, diagnosis)
        catchBlock.visitWritesBeyond(boundary, visitor, diagnosis)
    }

    override fun markEvaluationResultCaptured(withMutability: TypeMutability) {
        fallibleCode.markEvaluationResultCaptured(withMutability)
        catchBlock.markEvaluationResultCaptured(withMutability)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            fallibleCode.semanticAnalysisPhase3(diagnosis)
            catchBlock.semanticAnalysisPhase3(diagnosis)
        }
    }

    override fun toBackendIrExpression(): IrExpression {
        return IrTryCatchExpressionImpl(
            fallibleCode.toBackendIrAsImplicitEvaluationExpression(isEvaluationResultReferenceCounted),
            catchBlock.throwableVariable.backendIrDeclaration,
            catchBlock.catchCode.toBackendIrAsImplicitEvaluationExpression(isEvaluationResultReferenceCounted),
            type!!.toBackendIr(),
        )
    }
}

private class IrTryCatchExpressionImpl(
    override val fallibleCode: IrExpression,
    override val throwableVariable: IrVariableDeclaration,
    override val catchpad: IrExpression,
    override val evaluatesTo: IrType,
) : IrTryCatchExpression
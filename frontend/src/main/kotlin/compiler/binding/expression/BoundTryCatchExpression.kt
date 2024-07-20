package compiler.binding.expression

import compiler.ast.expression.AstTryCatchExpression
import compiler.ast.type.TypeMutability
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundExecutable
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.SideEffectPrediction.Companion.combineBranch
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
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

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = mutableSetOf<Reporting>()
            reportings.addAll(fallibleCode.semanticAnalysisPhase1())
            reportings.addAll(catchBlock.semanticAnalysisPhase1())

            return@phase1 reportings
        }
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        fallibleCode.setExpectedEvaluationResultType(type)
        catchBlock.setExpectedEvaluationResultType(type)
    }

    override fun markEvaluationResultUsed() {
        fallibleCode.markEvaluationResultUsed()
        catchBlock.markEvaluationResultUsed()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val reportings = mutableSetOf<Reporting>()
            reportings.addAll(fallibleCode.semanticAnalysisPhase2())
            reportings.addAll(catchBlock.semanticAnalysisPhase2())

            return@phase2 reportings
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        fallibleCode.setExpectedReturnType(type)
        catchBlock.setExpectedReturnType(type)
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        // note that even a catch-all cannot make code nothrow! Errors fall through
        fallibleCode.setNothrow(boundary)
        catchBlock.setNothrow(boundary)
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return fallibleCode.findReadsBeyond(boundary) + catchBlock.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<*>> {
        return fallibleCode.findWritesBeyond(boundary) + catchBlock.findWritesBeyond(boundary)
    }

    override fun markEvaluationResultCaptured(withMutability: TypeMutability) {
        fallibleCode.markEvaluationResultCaptured(withMutability)
        catchBlock.markEvaluationResultCaptured(withMutability)
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = mutableSetOf<Reporting>()
            reportings.addAll(fallibleCode.semanticAnalysisPhase3())
            reportings.addAll(catchBlock.semanticAnalysisPhase3())

            return@phase3 reportings
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
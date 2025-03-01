/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.binding.expression

import compiler.ast.IfExpression
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundCondition
import compiler.binding.BoundExecutable
import compiler.binding.ImpurityVisitor
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SideEffectPrediction
import compiler.binding.SideEffectPrediction.Companion.combineBranch
import compiler.binding.SideEffectPrediction.Companion.combineSequentialExecution
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MultiBranchJoinExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrConditionalBranch
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundIfExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: IfExpression,
    val condition: BoundCondition,
    val thenCode: BoundCodeChunk,
    val elseCode: BoundCodeChunk?
) : BoundExpression<IfExpression>, BoundExecutable<IfExpression> {
    override val throwBehavior: SideEffectPrediction? get() {
        val branches = thenCode.throwBehavior.combineBranch(if (elseCode == null) SideEffectPrediction.NEVER else elseCode.throwBehavior)
        return condition.throwBehavior.combineSequentialExecution(branches)
    }

    override val returnBehavior: SideEffectPrediction? get() {
        val branches = thenCode.returnBehavior.combineBranch(if (elseCode == null) SideEffectPrediction.NEVER else elseCode.returnBehavior)
        return condition.returnBehavior.combineSequentialExecution(branches)
    }

    override var type: BoundTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        type = context.swCtx.unit.baseReference

        condition.semanticAnalysisPhase1(diagnosis)
        thenCode.semanticAnalysisPhase1(diagnosis)
        elseCode?.semanticAnalysisPhase1(diagnosis)
    }

    private var isInExpressionContext = false

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        isInExpressionContext = true
        thenCode.setExpectedEvaluationResultType(type, diagnosis)
        elseCode?.setExpectedEvaluationResultType(type, diagnosis)
    }

    override fun markEvaluationResultUsed() {
        isInExpressionContext = true
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        condition.semanticAnalysisPhase2(diagnosis)
        thenCode.semanticAnalysisPhase2(diagnosis)
        elseCode?.semanticAnalysisPhase2(diagnosis)

        if (isInExpressionContext) {
            type = listOfNotNull(
                thenCode.type,
                elseCode?.type,
            )
                .takeUnless { it.isEmpty() }
                ?.reduce(BoundTypeReference::closestCommonSupertypeWith)
        }
    }

    override val modifiedContext: ExecutionScopedCTContext = if (elseCode != null) {
        MultiBranchJoinExecutionScopedCTContext(context, listOf(thenCode.modifiedContext, elseCode.modifiedContext))
    } else {
        SingleBranchJoinExecutionScopedCTContext(context, thenCode.modifiedContext)
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        condition.setNothrow(boundary)
        thenCode.setNothrow(boundary)
        elseCode?.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        condition.semanticAnalysisPhase3(diagnosis)
        thenCode.semanticAnalysisPhase3(diagnosis)
        elseCode?.semanticAnalysisPhase3(diagnosis)
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor, diagnosis: Diagnosis) {
        condition.visitReadsBeyond(boundary, visitor, diagnosis)
        thenCode.visitReadsBeyond(boundary, visitor, diagnosis)
        elseCode?.visitReadsBeyond(boundary, visitor, diagnosis)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor, diagnosis: Diagnosis) {
        condition.visitWritesBeyond(boundary, visitor, diagnosis)
        thenCode.visitWritesBeyond(boundary, visitor, diagnosis)
        elseCode?.visitWritesBeyond(boundary, visitor, diagnosis)
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        thenCode.setExpectedReturnType(type, diagnosis)
        elseCode?.setExpectedReturnType(type, diagnosis)
    }

    override val isEvaluationResultReferenceCounted get() = when {
        elseCode != null -> {
            // if either is implicitly refcounted, we have to add the reference counting on the other
            thenCode.isEvaluationResultReferenceCounted || elseCode.isEvaluationResultReferenceCounted
        }
        else -> {
            // elseCode == null, doesn't evaluate to either branch but to implicit unit -> not refcounted
            false
        }
    }

    override val isEvaluationResultAnchored: Boolean get() = when {
        elseCode != null -> {
            thenCode.isEvaluationResultAnchored && elseCode.isEvaluationResultAnchored
        }
        else -> {
            // elseCode == null, doesn't evaluate to either branch but to implicit unit -> that is static
            true
        }
    }

    override val isCompileTimeConstant = false

    override fun toBackendIrStatement(): IrExecutable {
        val conditionTemporary = IrCreateTemporaryValueImpl(condition.toBackendIrExpression())
        return IrCodeChunkImpl(listOf(
            conditionTemporary,
            IrConditionalBranchImpl(
                IrTemporaryValueReferenceImpl(conditionTemporary),
                thenCode.toBackendIrStatement(),
                elseCode?.toBackendIrStatement(),
            )
        ))
    }

    override fun toBackendIrExpression(): IrExpression {
        val conditionTemporary = IrCreateTemporaryValueImpl(condition.toBackendIrExpression())
        val ifTemporary = IrCreateTemporaryValueImpl(
            IrIfExpressionImpl(
                IrTemporaryValueReferenceImpl(conditionTemporary),
                thenCode.toBackendIrAsImplicitEvaluationExpression(isEvaluationResultReferenceCounted),
                elseCode?.toBackendIrAsImplicitEvaluationExpression(isEvaluationResultReferenceCounted),
                type!!.toBackendIr(),
            )
        )

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(
                conditionTemporary,
                ifTemporary,
            )),
            IrTemporaryValueReferenceImpl(ifTemporary),
        )
    }
}

internal class IrIfExpressionImpl(
    override val condition: IrTemporaryValueReference,
    override val thenBranch: IrImplicitEvaluationExpression,
    override val elseBranch: IrImplicitEvaluationExpression?,
    override val evaluatesTo: IrType,
) : IrIfExpression

internal class IrConditionalBranchImpl(
    override val condition: IrTemporaryValueReference,
    override val thenBranch: IrExecutable,
    override val elseBranch: IrExecutable?
) : IrConditionalBranch
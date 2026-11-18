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
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MultiBranchJoinExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.context.effect.VariableTypeRefinement
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.MissingElseBranchDiagnostic
import compiler.diagnostic.NothrowViolationDiagnostic
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
    private val contextForThen: MutableExecutionScopedCTContext,
    val thenCode: BoundCodeChunk,
    private val contextForElse: MutableExecutionScopedCTContext?,
    val elseCode: BoundCodeChunk?
) : BoundExpression<IfExpression>, BoundExecutable<IfExpression> {
    override var type: BoundTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        type = context.swCtx.unit.getBoundReferenceAssertNoTypeParameters(declaration.ifKeyword.span)

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
        thenCode.markEvaluationResultUsed()
        elseCode?.markEvaluationResultUsed()
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        thenCode.setEvaluationResultUsage(valueUsage)
        elseCode?.setEvaluationResultUsage(valueUsage)
    }

    /**
     * Where the condition was false; the context of the `else` branch, or an empty one if there is none. It carries the
     * implications of the condition being false, for the code after the `if` where the then branch doesn't complete
     * normally (e.g. `if isNull(v) { return }`).
     */
    private val contextWhenFalse: MutableExecutionScopedCTContext = contextForElse ?: MutableExecutionScopedCTContext.deriveFrom(condition.modifiedContext)

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        condition.semanticAnalysisPhase2(diagnosis)

        val implications = condition.implications
        VariableTypeRefinement.trackImplications(implications, BoundExpression.ImplyingResult.BOOL_TRUE, contextForThen)
        VariableTypeRefinement.trackImplications(implications, BoundExpression.ImplyingResult.BOOL_FALSE, contextWhenFalse)

        thenCode.semanticAnalysisPhase2(diagnosis)
        elseCode?.semanticAnalysisPhase2(diagnosis)

        if (isInExpressionContext && elseCode != null) {
            type = listOfNotNull(
                thenCode.type,
                elseCode.type,
            )
                .takeUnless { it.isEmpty() }
                ?.reduce(BoundTypeReference::closestCommonSupertypeWith)
        } else if (isInExpressionContext) {
            val thenType = thenCode.type
            if (thenType != null && !thenType.isUnitOrNothing) {
                diagnosis.add(MissingElseBranchDiagnostic(declaration.ifKeyword))
                type = thenType
            }
        }
    }

    private val BoundTypeReference.isUnitOrNothing: Boolean
        get() = this is RootResolvedTypeReference && (baseType == context.swCtx.unit || baseType == context.swCtx.nothing)

    override val modifiedContext: ExecutionScopedCTContext = if (elseCode != null) {
        MultiBranchJoinExecutionScopedCTContext(condition.modifiedContext, listOf(thenCode.modifiedContext, elseCode.modifiedContext))
    } else {
        SingleBranchJoinExecutionScopedCTContext(condition.modifiedContext, thenCode.modifiedContext, contextWhenFalse)
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        condition.setNothrow(boundary)
        thenCode.setNothrow(boundary)
        elseCode?.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        condition.semanticAnalysisPhase3(diagnosis)
        thenCode.semanticAnalysisPhase3(diagnosis)
        elseCode?.semanticAnalysisPhase3(diagnosis)
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        condition.visitReadsBeyond(boundary, visitor)
        thenCode.visitReadsBeyond(boundary, visitor)
        elseCode?.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        condition.visitWritesBeyond(boundary, visitor)
        thenCode.visitWritesBeyond(boundary, visitor)
        elseCode?.visitWritesBeyond(boundary, visitor)
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
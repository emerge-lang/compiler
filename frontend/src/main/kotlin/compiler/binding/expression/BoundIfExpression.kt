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

import compiler.ast.Expression
import compiler.ast.IfExpression
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundExecutable
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BuiltinBoolean
import compiler.binding.type.isAssignableTo
import compiler.nullableAnd
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundIfExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: IfExpression,
    val condition: BoundExpression<Expression>,
    val thenCode: BoundCodeChunk,
    val elseCode: BoundCodeChunk?
) : BoundExpression<IfExpression>, BoundExecutable<IfExpression> {
    override val isGuaranteedToThrow: Boolean
        get() = thenCode.isGuaranteedToThrow nullableAnd (elseCode?.isGuaranteedToThrow ?: false)

    override val isGuaranteedToReturn: Boolean
        get() {
            if (elseCode == null) {
                return false
            }
            else {
                return thenCode.isGuaranteedToReturn nullableAnd elseCode.isGuaranteedToReturn
            }
        }

    override var type: BoundTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        type = context.swCtx.unitBaseType.baseReference

        var reportings = condition.semanticAnalysisPhase1() + thenCode.semanticAnalysisPhase1()

        val elseCodeReportings = elseCode?.semanticAnalysisPhase1()
        if (elseCodeReportings != null) {
            reportings = reportings + elseCodeReportings
        }

        return reportings
    }

    private var isInExpressionContext = false
    override fun requireImplicitEvaluationTo(type: BoundTypeReference) {
        isInExpressionContext = true
        thenCode.requireImplicitEvaluationTo(type)
        elseCode?.requireImplicitEvaluationTo(type)
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        requireImplicitEvaluationTo(type)
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        var reportings = condition.semanticAnalysisPhase2() + thenCode.semanticAnalysisPhase2()

        val elseCodeReportings = elseCode?.semanticAnalysisPhase2()
        if (elseCodeReportings != null) {
            reportings = reportings + elseCodeReportings
        }

        if (isInExpressionContext) {
            type = listOfNotNull(
                thenCode.implicitEvaluationResultType,
                elseCode?.implicitEvaluationResultType
            )
                .takeUnless { it.isEmpty() }
                ?.reduce(BoundTypeReference::closestCommonSupertypeWith)
        }

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        reportings.addAll(condition.semanticAnalysisPhase3())
        reportings.addAll(thenCode.semanticAnalysisPhase3())

        if (elseCode != null) {
            reportings.addAll(elseCode.semanticAnalysisPhase3())
        }

        if (condition.type != null) {
            val conditionType = condition.type!!
            if (!conditionType.isAssignableTo(BuiltinBoolean.baseReference)) {
                reportings.add(Reporting.conditionIsNotBoolean(condition, condition.declaration.sourceLocation))
            }
        }

        condition.findWritesBeyond(context)
            .map(Reporting::mutationInCondition)
            .forEach(reportings::add)

        return reportings
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        thenCode.setExpectedReturnType(type)
        elseCode?.setExpectedReturnType(type)
    }

    override val isEvaluationResultReferenceCounted get() = when {
        elseCode != null -> {
            // if either is implicitly refcounted, we have to add the reference counting on the other
            thenCode.isImplicitEvaluationResultReferenceCounted || elseCode.isImplicitEvaluationResultReferenceCounted
        }
        else -> {
            // elseCode == null, doesn't evaluate to either branch but to implicit unit -> not refcounted
            false
        }
    }

    override fun toBackendIrExpression(): IrExpression {
        val thenResultNeedsToIncludeRefCount = isEvaluationResultReferenceCounted && !thenCode.isImplicitEvaluationResultReferenceCounted
        val elseResultNeedsToIncludeRefCount = isEvaluationResultReferenceCounted && !(elseCode?.isImplicitEvaluationResultReferenceCounted ?: true)

        val conditionTemporary = IrCreateTemporaryValueImpl(condition.toBackendIrExpression())
        val ifTemporary = IrCreateTemporaryValueImpl(
            IrIfExpressionImpl(
                IrTemporaryValueReferenceImpl(conditionTemporary),
                thenCode.toBackendIrAsImplicitEvaluationExpression(thenResultNeedsToIncludeRefCount),
                elseCode?.toBackendIrAsImplicitEvaluationExpression(elseResultNeedsToIncludeRefCount),
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

private class IrIfExpressionImpl(
    override val condition: IrTemporaryValueReference,
    override val thenBranch: IrImplicitEvaluationExpression,
    override val elseBranch: IrImplicitEvaluationExpression?,
    override val evaluatesTo: IrType,
) : IrIfExpression
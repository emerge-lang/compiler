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

import compiler.ast.expression.NullLiteralExpression
import compiler.ast.type.TypeReference
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNullLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundNullLiteralExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: NullLiteralExpression
) : BoundLiteralExpression<NullLiteralExpression>
{
    private var expectedType: BoundTypeReference? = null
    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        expectedType = type
    }

    override val type: BoundTypeReference
        get() = context.swCtx.getBottomType(declaration.span)
            .withCombinedNullability(TypeReference.Nullability.NULLABLE)

    override val throwBehavior = SideEffectPrediction.NEVER
    override val returnBehavior = SideEffectPrediction.NEVER

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {}

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored = true
    override val isCompileTimeConstant = true

    override fun toBackendIrExpression(): IrExpression {
        return IrNullLiteralExpressionImpl(type.toBackendIr())
    }
}

internal class IrNullLiteralExpressionImpl(
    override val evaluatesTo: IrType,
) : IrNullLiteralExpression
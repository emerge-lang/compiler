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
import compiler.binding.BoundStatement
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Reporting
import compiler.reportings.SideEffectBoundary
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNullLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundNullLiteralExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: NullLiteralExpression
) : BoundExpression<NullLiteralExpression>
{
    private var expectedType: BoundTypeReference? = null
    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        expectedType = type
    }

    override val type: BoundTypeReference?
        get() = expectedType?.withCombinedNullability(TypeReference.Nullability.NULLABLE)

    override val throwBehavior = SideEffectPrediction.NEVER
    override val returnBehavior = SideEffectPrediction.NEVER

    override fun semanticAnalysisPhase1(): Collection<Reporting> = emptySet()
    override fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()
    override fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> = emptySet()
    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> = emptySet()
    override fun setNothrow(boundary: SideEffectBoundary) {}

    override val isEvaluationResultReferenceCounted = false
    override val isCompileTimeConstant = true

    override fun toBackendIrExpression(): IrExpression {
        return IrNullLiteralExpressionImpl(type?.toBackendIr() ?: context.swCtx.any.baseReference.withCombinedNullability(TypeReference.Nullability.NULLABLE).toBackendIr())
    }
}

private class IrNullLiteralExpressionImpl(
    override val evaluatesTo: IrType,
) : IrNullLiteralExpression
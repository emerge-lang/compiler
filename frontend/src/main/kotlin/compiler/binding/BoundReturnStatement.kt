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

package compiler.binding

import compiler.ast.ReturnStatement
import compiler.ast.expression.IdentifierExpression
import compiler.ast.type.TypeMutability
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.IdentifierToken
import compiler.reportings.Reporting
import compiler.reportings.ReturnTypeMismatchReporting
import compiler.reportings.SideEffectBoundary
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

class BoundReturnStatement(
    override val context: ExecutionScopedCTContext,
    override val declaration: ReturnStatement
) : BoundStatement<ReturnStatement> {

    private var expectedReturnType: BoundTypeReference? = null

    val expression = declaration.expression?.bindTo(context)

    override val returnBehavior = SideEffectPrediction.GUARANTEED // this is the core LoC that makes the property work big-scale
    override val throwBehavior get() = if (expression == null) SideEffectPrediction.NEVER else expression.throwBehavior

    override val implicitEvaluationResultType = null

    override fun requireImplicitEvaluationTo(type: BoundTypeReference) {

    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return expression?.semanticAnalysisPhase1() ?: emptySet()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        expression?.markEvaluationResultUsed()
        return expression?.semanticAnalysisPhase2() ?: emptySet()
    }

    override fun setNothrow(boundary: SideEffectBoundary) {
        expression?.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        val expectedReturnType = this.expectedReturnType
        expression?.markEvaluationResultCaptured(expectedReturnType?.mutability ?: TypeMutability.READONLY)
        expression?.semanticAnalysisPhase3()?.let(reportings::addAll)

        if (expectedReturnType == null) {
            return reportings + Reporting.consecutive(
                "Cannot check return value type because the expected return type is not known",
                declaration.span
            )
        }

        val expressionType = expression?.type

        if (expressionType != null) {
            expressionType.evaluateAssignabilityTo(expectedReturnType, declaration.span)
                ?.let {
                    reportings.add(ReturnTypeMismatchReporting(it))
                }
        }

        if (expectedReturnType is RootResolvedTypeReference && expectedReturnType.baseType != context.swCtx.unit && expression == null) {
            reportings.add(Reporting.missingReturnValue(this, expectedReturnType))
        }

        return reportings
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        expectedReturnType = type
        expression?.setExpectedEvaluationResultType(type)
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return this.expression?.findReadsBeyond(boundary) ?: emptySet()
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        return this.expression?.findWritesBeyond(boundary) ?: emptySet()
    }

    override fun toBackendIrStatement(): IrExecutable {
        val actualExpression: BoundExpression<*> = this.expression ?: run {
            // TODO: this is a dirty hack, Unit could be aliased in this context
            val ast = IdentifierExpression(IdentifierToken("Unit", declaration.returnKeyword.span))
            val bound = ast.bindTo(context)
            check(bound.semanticAnalysisPhase1().isEmpty())
            check(bound.semanticAnalysisPhase2().isEmpty())
            check(bound.semanticAnalysisPhase3().isEmpty())
            bound
        }

        val valueTemporary = IrCreateTemporaryValueImpl(actualExpression.toBackendIrExpression())
        val valueTemporaryRefIncrement = IrCreateStrongReferenceStatementImpl(valueTemporary).takeUnless { actualExpression.isEvaluationResultReferenceCounted }
        return IrCodeChunkImpl(
            listOfNotNull(valueTemporary, valueTemporaryRefIncrement) +
            context.getFunctionDeferredCode().map { it.toBackendIrStatement() }.toList() +
            listOf(IrReturnStatementImpl(IrTemporaryValueReferenceImpl(valueTemporary)))
        )
    }
}

internal class IrReturnStatementImpl(override val value: IrTemporaryValueReference) : IrReturnStatement
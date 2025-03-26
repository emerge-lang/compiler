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

import compiler.InternalCompilerError
import compiler.ast.ReturnExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.ImpurityVisitor
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeVariable
import compiler.binding.type.UnresolvedType
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.consecutive
import compiler.diagnostic.missingReturnValue
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

class BoundReturnExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: ReturnExpression
) : BoundScopeAbortingExpression() {

    private var expectedReturnType: BoundTypeReference? = null

    val expression = declaration.expression?.bindTo(context)

    override val throwBehavior get() = if (expression == null) SideEffectPrediction.NEVER else expression.throwBehavior
    override val returnBehavior get() = when (throwBehavior) {
        SideEffectPrediction.GUARANTEED -> SideEffectPrediction.NEVER
        else -> SideEffectPrediction.GUARANTEED
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        expression?.semanticAnalysisPhase1(diagnosis)
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        expression?.markEvaluationResultUsed()
        expression?.semanticAnalysisPhase2(diagnosis)
        expression?.setUsageContext(
            expectedReturnType
                ?: context.swCtx.any.baseReference
                    .withCombinedNullability(TypeReference.Nullability.NULLABLE)
                    .withMutability(TypeMutability.READONLY)
        )
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        expression?.setNothrow(boundary)
    }

    override fun setUsageContext(usedAsType: BoundTypeReference) {
        // nothing to do; the evaluation result type of "return" is Nothing
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        val expectedReturnType = this.expectedReturnType
        expression?.markEvaluationResultCaptured(expectedReturnType?.mutability ?: TypeMutability.READONLY)
        expression?.semanticAnalysisPhase3(diagnosis)

        if (expectedReturnType == null) {
            diagnosis.consecutive(
                "Cannot check return value type because the expected return type is not known",
                declaration.span
            )
            return
        }

        val expressionType = expression?.type

        if (expressionType != null) {
            expressionType.evaluateAssignabilityTo(expectedReturnType, declaration.span)
                ?.let(::ReturnTypeMismatchDiagnostic)
                ?.let(diagnosis::add)
        }

        if (expectedReturnType is RootResolvedTypeReference && expectedReturnType.baseType != context.swCtx.unit && expression == null) {
            diagnosis.missingReturnValue(this, expectedReturnType)
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        expectedReturnType = type
        expression?.setExpectedEvaluationResultType(type, diagnosis)
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        expression?.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        expression?.visitWritesBeyond(boundary, visitor)
    }

    override fun toBackendIrStatement(): IrExecutable {
        val actualExpression: BoundExpression<*> = this.expression ?: run {
            val ast = InvocationExpression(
                MemberAccessExpression(
                    IdentifierExpression(IdentifierToken("Unit", declaration.returnKeyword.span)),
                    OperatorToken(Operator.DOT),
                    IdentifierToken("instance", declaration.returnKeyword.span),
                ),
                null,
                emptyList(),
                declaration.returnKeyword.span.deriveGenerated(),
            )
            val bound = ast.bindTo(context)
            bound.semanticAnalysisPhase1(Diagnosis.failOnError())
            bound.semanticAnalysisPhase2(Diagnosis.failOnError())
            bound.semanticAnalysisPhase3(Diagnosis.failOnError())
            bound
        }

        if (actualExpression.type!!.isNothing) {
            return actualExpression.toBackendIrStatement()
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

private val BoundTypeReference.isNothing: Boolean get() = !isNullable && when (this) {
    is RootResolvedTypeReference -> this.baseType == this.baseType.context.swCtx.nothing
    is BoundTypeArgument -> this.type.isNothing
    is GenericTypeReference -> this.effectiveBound.isNothing
    is NullableTypeReference -> false
    is UnresolvedType -> false
    is TypeVariable -> throw InternalCompilerError("type inference not completed")
}
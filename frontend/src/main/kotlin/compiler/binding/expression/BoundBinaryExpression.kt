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

import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.binding.BoundStatement
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

class BoundBinaryExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: BinaryExpression,
    val leftHandSide: BoundExpression<*>,
    val operator: Operator,
    val rightHandSide: BoundExpression<*>
) : BoundExpression<BinaryExpression> {

    private val hiddenInvocation: BoundInvocationExpression = InvocationExpression(
            MemberAccessExpression(
                    leftHandSide.declaration,
                    OperatorToken(Operator.DOT, declaration.op.span),
                    IdentifierToken(operatorFunctionName(operator), declaration.op.span)
            ),
            null,
            listOf(rightHandSide.declaration),
            leftHandSide.declaration.span .. rightHandSide.declaration.span,
        )
            .bindTo(context)

    override val type: BoundTypeReference?
        get() = hiddenInvocation.type

    override val throwBehavior get() = hiddenInvocation.throwBehavior
    override val returnBehavior get() = hiddenInvocation.returnBehavior

    override fun semanticAnalysisPhase1() = hiddenInvocation.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        reportings.addAll(hiddenInvocation.semanticAnalysisPhase2())

        val opFn = hiddenInvocation.functionToInvoke
        if (opFn != null) {
            if (!opFn.attributes.isDeclaredOperator) {
                reportings.add(Reporting.modifierError("Function ${opFn.canonicalName} cannot be used as an operator: the operator modifier is missing", declaration.span))
            }
        }

        return reportings
    }

    override fun semanticAnalysisPhase3() = hiddenInvocation.semanticAnalysisPhase3()

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return hiddenInvocation.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        return hiddenInvocation.findWritesBeyond(boundary)
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do, as one could only correlate this with the return value
        // of the operator function. But overload resolution based on return type
        // is not a thing in Emerge
    }

    override val isEvaluationResultReferenceCounted get() = hiddenInvocation.isEvaluationResultReferenceCounted
    override val isCompileTimeConstant get() = hiddenInvocation.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        return hiddenInvocation.toBackendIrExpression()
    }
}

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "op" + op.name[0].uppercase() + op.name.substring(1).lowercase()
}
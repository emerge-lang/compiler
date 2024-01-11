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

import compiler.ast.Executable
import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.Expression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.FunctionModifier
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.nullableOr
import compiler.reportings.Reporting

class BoundBinaryExpression(
    override val context: CTContext,
    override val declaration: BinaryExpression,
    val leftHandSide: BoundExpression<*>,
    val operator: Operator,
    val rightHandSide: BoundExpression<*>
) : BoundExpression<BinaryExpression> {

    private val hiddenInvocation: BoundInvocationExpression = InvocationExpression(
            MemberAccessExpression(
                    leftHandSide.declaration as Expression<*>,
                    OperatorToken(Operator.DOT, declaration.op.sourceLocation),
                    IdentifierToken(operatorFunctionName(operator), declaration.op.sourceLocation)
            ),
            emptyList(),
            listOf(rightHandSide.declaration as Expression<*>),
        )
            .bindTo(context)

    override val type: BoundTypeReference?
        get() = hiddenInvocation.type

    override val isGuaranteedToThrow: Boolean?
        get() = leftHandSide.isGuaranteedToThrow nullableOr rightHandSide.isGuaranteedToThrow

    override fun semanticAnalysisPhase1() = hiddenInvocation.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        reportings.addAll(hiddenInvocation.semanticAnalysisPhase2())

        val opFn = hiddenInvocation.dispatchedFunction
        if (opFn != null) {
            if (FunctionModifier.OPERATOR !in opFn.modifiers) {
                reportings.add(Reporting.modifierError("Function $opFn cannot be used as an operator: the operator modifier is missing", declaration.sourceLocation))
            }
        }

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return hiddenInvocation.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return hiddenInvocation.findWritesBeyond(boundary)
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do, as one could only correlate this with the return value
        // of the operator function. But overload resolution based on return type
        // is not a thing in this language
    }
}

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "op" + op.name[0].uppercase() + op.name.substring(1).lowercase()
}
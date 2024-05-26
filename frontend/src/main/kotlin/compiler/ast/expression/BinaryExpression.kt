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

package compiler.ast.expression

import compiler.InternalCompilerError
import compiler.ast.AstSemanticOperator
import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundBinaryExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

private val OPERATOR_FUNCTION_NAME_MAPPING: Map<Any, String> = mapOf(
    Keyword.AND to "and",
    Keyword.OR to "or",
    Keyword.XOR to "xor",
    Operator.PLUS to "plus",
    Operator.MINUS to "minus",
    Operator.DIVIDE to "divideBy",
    Operator.TIMES to "times",
    Operator.EQUALS to "equals",
)

class BinaryExpression(
    val leftHandSide: Expression,
    val operator: AstSemanticOperator,
    val rightHandSide: Expression
) : Expression {
    override val span = leftHandSide.span

    // simply rewrite to an invocation
    override fun bindTo(context: ExecutionScopedCTContext): BoundBinaryExpression {
        val functionName = OPERATOR_FUNCTION_NAME_MAPPING[operator.operatorElement]
            ?: throw InternalCompilerError("Unsupported binary operator ${operator.token}")

        val opDerivedLocation = operator.token.span.deriveGenerated()
        val hiddenInvocation = InvocationExpression(
            MemberAccessExpression(
                leftHandSide,
                OperatorToken(Operator.DOT, opDerivedLocation),
                IdentifierToken(functionName, opDerivedLocation)
            ),
            null,
            listOf(rightHandSide),
            leftHandSide.span..rightHandSide.span,
        ).bindTo(context)

        return BoundBinaryExpression(
            context,
            this,
            hiddenInvocation,
        )
    }
}
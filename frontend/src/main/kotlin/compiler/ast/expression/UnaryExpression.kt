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

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundUnaryExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

class UnaryExpression(
    val operatorToken: OperatorToken,
    val valueExpression: Expression,
):Expression {
    override val sourceLocation = valueExpression.sourceLocation

    override fun bindTo(context: ExecutionScopedCTContext): BoundUnaryExpression {
        val functionName = operatorFunctionName(operatorToken.operator)
        val hiddenInvocation = InvocationExpression(
            MemberAccessExpression(
                valueExpression,
                OperatorToken(Operator.DOT, operatorToken.sourceLocation),
                IdentifierToken(functionName, operatorToken.sourceLocation),
            ),
            emptyList(),
            emptyList(),
            operatorToken.sourceLocation .. valueExpression.sourceLocation,
        )

        return BoundUnaryExpression(
            context,
            this,
            hiddenInvocation.bindTo(context),
        )
    }
}

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "unary" + op.name[0].uppercase() + op.name.substring(1).lowercase()
}
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

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

/**
 * Models member access (`obj.member`). When evaluated like usual, attempts to access defined properties and extension
 * properties only.
 *
 * Member method invocation is handled by [InvocationExpression]. When its receiver expression is a [MemberAccessExpression],
 * it leftHandSide tries to resolve a member function with the [memberName] before evaluating this expression.
 *
 * @param accessOperatorToken must be either [Operator.DOT] or [Operator.SAFEDOT]
 */
class MemberAccessExpression(
        val valueExpression: Expression<*>,
        val accessOperatorToken: OperatorToken,
        val memberName: IdentifierToken
) : Expression<BoundMemberAccessExpression> {
    override val sourceLocation = valueExpression.sourceLocation

    override fun bindTo(context: CTContext): BoundMemberAccessExpression {
        return BoundMemberAccessExpression(
            context,
            this,
            valueExpression.bindTo(context),
            accessOperatorToken.operator == Operator.SAFEDOT,
            memberName.value
        )
    }
}
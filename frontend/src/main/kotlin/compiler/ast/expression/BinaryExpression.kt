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
import compiler.binding.expression.BoundBinaryExpression
import compiler.lexer.OperatorToken

class BinaryExpression(
    val leftHandSide: Expression,
    val op: OperatorToken,
    val rightHandSide: Expression
) : Expression {
    override val sourceLocation = leftHandSide.sourceLocation

    // simply rewrite to an invocation
    override fun bindTo(context: ExecutionScopedCTContext) = BoundBinaryExpression(
            context,
            this,
            leftHandSide.bindTo(context),
            op.operator,
            rightHandSide.bindTo(context)
    )
}
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

package compiler.reportings

import compiler.binding.expression.BoundExpression
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

/**
 * Reported when an expression is used in a way that requires it to be non-null but the type of the expression is nullable.
 */
data class UnsafeObjectTraversalDiagnostic(
    val nullableExpression: BoundExpression<*>,
    val faultyAccessOperator: OperatorToken
) : Diagnostic(
    Level.ERROR,
    "Receiver expression could evaluate to null (type is ${nullableExpression.type}). " +
        "Assert non null (operator ${Operator.NOTNULL.text}) or use the safe object traversal operator ${Operator.SAFEDOT.text}",
    faultyAccessOperator.span,
) {
    override fun toString() = super.toString()
}
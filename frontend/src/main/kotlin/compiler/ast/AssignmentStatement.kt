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

package compiler.ast

import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundAssignmentStatement
import compiler.lexer.KeywordToken
import compiler.lexer.OperatorToken

class AssignmentStatement(
    val setKeyword: KeywordToken,
    val targetExpression: Expression,
    val assignmentOperatorToken: OperatorToken,
    val valueExpression: Expression
) : Statement {

    override val sourceLocation = setKeyword.sourceLocation

    override fun bindTo(context: ExecutionScopedCTContext) = BoundAssignmentStatement(
        context,
        this,
        targetExpression.bindTo(context),
        valueExpression.bindTo(context)
    )
}
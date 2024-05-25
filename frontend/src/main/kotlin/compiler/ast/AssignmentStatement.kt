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

import compiler.ast.expression.AstIndexAccessExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.binding.BoundIllegalTargetAssignmentStatement
import compiler.binding.BoundObjectMemberAssignmentStatement
import compiler.binding.BoundStatement
import compiler.binding.BoundVariableAssignmentStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

class AssignmentStatement(
    val setKeyword: KeywordToken,
    val targetExpression: Expression,
    val assignmentOperatorToken: OperatorToken,
    val valueExpression: Expression
) : Statement {

    override val span = setKeyword.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
        when (targetExpression) {
            is IdentifierExpression -> {
                val boundValue = valueExpression.bindTo(context)
                return BoundVariableAssignmentStatement(
                    boundValue.modifiedContext,
                    this,
                    targetExpression.identifier,
                    boundValue
                )
            }
            is MemberAccessExpression -> {
                val boundTarget = targetExpression.bindTo(context)
                val boundValue = valueExpression.bindTo(boundTarget.modifiedContext)
                return BoundObjectMemberAssignmentStatement(
                    boundValue.modifiedContext,
                    this,
                    boundTarget,
                    boundValue,
                )
            }
            is AstIndexAccessExpression -> {
                val generatedSpan = span.deriveGenerated()
                val hiddenInvocation = InvocationExpression(
                    MemberAccessExpression(
                        targetExpression.valueExpression,
                        OperatorToken(Operator.DOT, generatedSpan),
                        IdentifierToken("set", generatedSpan),
                    ),
                    null,
                    listOf(
                        targetExpression.indexExpression,
                        valueExpression,
                    ),
                    generatedSpan,
                )
                return hiddenInvocation.bindTo(context)
            }
            else -> {
                val boundTarget = targetExpression.bindTo(context)
                val boundValue = valueExpression.bindTo(boundTarget.modifiedContext)
                return BoundIllegalTargetAssignmentStatement(
                    boundValue.modifiedContext,
                    this,
                    boundTarget,
                    boundValue,
                )
            }
        }
    }
}
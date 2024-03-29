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
import compiler.ast.Expression
import compiler.ast.Expression.Companion.chain
import compiler.ast.type.TypeArgument
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundInvocationExpression
import compiler.lexer.SourceLocation

class InvocationExpression(
    /**
     * The target of the invocation. e.g.:
     * * `doStuff()` => `IdentifierExpression(doStuff)`
     * * `obj.doStuff()` => `MemberAccessExpression(obj, doStuff)`
     */
    val targetExpression:Expression,
    val typeArguments: List<TypeArgument>,
    val argumentExpressions: List<Expression>
) :Expression {
    override val sourceLocation: SourceLocation = when(targetExpression) {
        is MemberAccessExpression -> targetExpression.memberName.sourceLocation
        else -> targetExpression.sourceLocation
    }

    override fun bindTo(context: ExecutionScopedCTContext): BoundInvocationExpression {
        // bind all the parameters
        val boundArguments = argumentExpressions.chain(context).toList()
        val contextAfterArguments = boundArguments.lastOrNull()?.modifiedContext ?: context

        if (targetExpression is MemberAccessExpression) {
            return BoundInvocationExpression(
                contextAfterArguments,
                this,
                targetExpression.valueExpression.bindTo(context),
                targetExpression.memberName,
                boundArguments,
            )
        }
        else if (targetExpression is IdentifierExpression) {
            return BoundInvocationExpression(
                contextAfterArguments,
                this,
                null,
                targetExpression.identifier,
                boundArguments,
            )
        }
        else throw InternalCompilerError("What the heck is going on?? The parser should never have allowed this!")
    }
}
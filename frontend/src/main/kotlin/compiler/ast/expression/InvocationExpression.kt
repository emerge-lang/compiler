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
import compiler.ast.Executable
import compiler.ast.type.TypeArgument
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundInvocationExpression
import compiler.lexer.SourceLocation

class InvocationExpression(
    /**
     * The target of the invocation. e.g.:
     * * `doStuff()` => `IdentifierExpression(doStuff)`
     * * `obj.doStuff()` => `MemberAccessExpression(obj, doStuff)`
     */
    val targetExpression: Expression<*>,
    val typeArguments: List<TypeArgument>,
    val valueArgumentExpressions: List<Expression<*>>
) : Expression<BoundInvocationExpression>, Executable<BoundInvocationExpression> {
    override val sourceLocation: SourceLocation = when(targetExpression) {
        is MemberAccessExpression -> targetExpression.memberName.sourceLocation
        else -> targetExpression.sourceLocation
    }

    override fun bindTo(context: CTContext): BoundInvocationExpression {
        // bind all the parameters
        val boundParameterValueExprs = valueArgumentExpressions.map { it.bindTo(context) }

        if (targetExpression is MemberAccessExpression) {
            return BoundInvocationExpression(
                context,
                this,
                targetExpression.valueExpression.bindTo(context),
                targetExpression.memberName,
                boundParameterValueExprs
            )
        }
        else if (targetExpression is IdentifierExpression) {
            return BoundInvocationExpression(
                    context,
                    this,
                    null,
                    targetExpression.identifier,
                    boundParameterValueExprs
            )
        }
        else throw InternalCompilerError("What the heck is going on?? The parser should never have allowed this!")
    }
}
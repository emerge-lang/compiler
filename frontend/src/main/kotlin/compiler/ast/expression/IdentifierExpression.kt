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
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundIdentifierExpression
import compiler.lexer.IdentifierToken

/**
 * A expression that evaluates using an identigier (variable reference, type reference)
 *
 * The [bindTo] method on this class assumes that the identifier references a variable. If the
 * identifier expression is used within a context where it may denote something else that logic is handled by the
 * enclosing context. Some examples:
 * * within a method invocation: [InvocationExpression] may read the [identifier] and treat it as a method name
 * * within a constructor invocation: [InvocationExpression] may read the [identifier] and treat it as a type name
 */
class IdentifierExpression(val identifier: IdentifierToken) :Expression {
    override val sourceLocation = identifier.sourceLocation

    override fun bindTo(context: CTContext): BoundIdentifierExpression {
        return BoundIdentifierExpression(context, this)
    }
}
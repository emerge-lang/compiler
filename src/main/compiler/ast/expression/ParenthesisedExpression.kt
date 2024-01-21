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

package compiler.ast.expression;

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.lexer.SourceLocation

/**
 * Wraps another [Expression] in order to influence evaluation order and operator precedence. The evidence of the
 * parenthesis is lost when binding this to a context: [.bindTo(CTContext)] delegates to [Expression.bindTo] of [nested].
 */
class ParenthesisedExpression<out NestedBoundType : BoundExpression<*>>(val nested: Expression<NestedBoundType>, override val sourceLocation: SourceLocation) : Expression<BoundExpression<*>> {
    override fun bindTo(context: CTContext): NestedBoundType {
        return nested.bindTo(context)
    }
}

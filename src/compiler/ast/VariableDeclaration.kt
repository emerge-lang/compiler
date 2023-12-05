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

import compiler.ast.expression.Expression
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

open class VariableDeclaration(
    override val declaredAt: SourceLocation,
    val typeMutability: TypeMutability?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val isAssignable: Boolean,
    val initializerExpression: Expression<*>?
) : Declaration, Executable<BoundVariable> {
    override val sourceLocation get() = declaredAt

    override fun bindTo(context: CTContext): BoundVariable = BoundVariable(context, this, initializerExpression?.bindTo(context))
}
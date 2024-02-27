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

import compiler.ast.type.TypeReference
import compiler.binding.BoundVariable
import compiler.binding.context.ExecutionScopedCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken
import compiler.lexer.SourceLocation

open class VariableDeclaration(
    override val declaredAt: SourceLocation,
    val varToken: KeywordToken?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val initializerExpression: Expression?
) : Statement, AstFileLevelDeclaration {
    override val sourceLocation get() = declaredAt
    val isReAssignable: Boolean = varToken != null

    override fun bindTo(context: ExecutionScopedCTContext): BoundVariable = bindTo(context, BoundVariable.Kind.VARIABLE)
    fun bindToAsParameter(context: ExecutionScopedCTContext): BoundVariable = bindTo(context, BoundVariable.Kind.PARAMETER)
    private fun bindTo(context: ExecutionScopedCTContext, kind: BoundVariable.Kind): BoundVariable = BoundVariable(
        context,
        this,
        initializerExpression?.bindTo(context),
        kind,
    )
}
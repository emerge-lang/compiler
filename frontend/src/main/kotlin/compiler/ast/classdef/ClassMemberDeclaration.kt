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

package compiler.ast.classdef

import compiler.ast.ASTVisibilityModifier
import compiler.ast.Expression
import compiler.ast.type.TypeReference
import compiler.binding.classdef.ClassContext
import compiler.binding.classdef.ClassMemberVariable
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

class ClassMemberDeclaration(
    val declaredAt: SourceLocation,
    val visibilityModifier: ASTVisibilityModifier?,
    val name: IdentifierToken,
    val type: TypeReference,
    val defaultValue: Expression?
) {
    init {
        check(defaultValue == null) {
            "Default values are not well defined at this point"
        }
    }
    fun bindTo(context: ClassContext): ClassMemberVariable {
        return ClassMemberVariable(
            context,
            this,
            null,
        )
    }
}
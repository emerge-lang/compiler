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

package compiler.ast.struct

import compiler.ast.Bindable
import compiler.ast.Declaration
import compiler.binding.context.CTContext
import compiler.binding.struct.Struct
import compiler.binding.struct.StructContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

class StructDeclaration(
    override val declaredAt: SourceLocation,
    val name: IdentifierToken,
    val memberDeclarations: Set<StructMemberDeclaration>
) : Declaration, Bindable<Struct> {
    override fun bindTo(context: CTContext): Struct {
        val structContext = StructContext(context)

        return Struct(
            structContext,
            this,
            memberDeclarations.map { it.bindTo(structContext) }.toSet()
        )
    }
}
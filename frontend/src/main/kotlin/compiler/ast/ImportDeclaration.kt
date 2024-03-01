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

import compiler.binding.BoundImportDeclaration
import compiler.binding.context.CTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

/**
 * An import statement
 */
class ImportDeclaration(
    override val declaredAt: SourceLocation,
    /** The identifiers in order of the source: `import pkg1.pkg2.component` => `[pkg1, pkg2, component]` */
    val identifiers: List<IdentifierToken>
) : AstFileLevelDeclaration {

    fun bindTo(context: CTContext): BoundImportDeclaration {
        return BoundImportDeclaration(context, this)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other?.javaClass != javaClass) return false

        other as ImportDeclaration

        if (identifiers != other.identifiers) return false

        return true
    }

    override fun hashCode(): Int {
        return identifiers.hashCode()
    }
}
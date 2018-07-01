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

/** (At least in the AST) has an access modifier. */
interface ASTVisibilityModified {
    var accessModifier: ASTVisibilityModifier
}

sealed class ASTVisibilityModifier {
    companion object {
        val DEFAULT: ASTVisibilityModifier = InternalASTVisibilityModifier.INSTANCE
    }
}

class PrivateASTVisibilityModifier private constructor() : ASTVisibilityModifier() {
    companion object {
        val INSTANCE = PrivateASTVisibilityModifier()
    }
}

class ProtectedASTVisibilityModifier private constructor() : ASTVisibilityModifier() {
    companion object {
        val INSTANCE = ProtectedASTVisibilityModifier()
    }
}

class QualifiedASTProtectedVisibilityModifier(val qualifier: Array<String>) : ASTVisibilityModifier()

class InternalASTVisibilityModifier private constructor() : ASTVisibilityModifier() {
    companion object {
        val INSTANCE = InternalASTVisibilityModifier()
    }
}

class ExportASTVisibilityModifier private constructor() : ASTVisibilityModifier() {
    companion object {
        val INSTANCE = ExportASTVisibilityModifier()
    }
}

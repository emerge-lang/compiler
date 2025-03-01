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

package compiler.diagnostic

import compiler.ast.VariableDeclaration

/**
 * Reported when a variable is declared within a context where a variable with the same name
 * already exists and cannot be shadowed.
 */
data class MultipleVariableDeclarationsDiagnostic(
    val originalDeclaration: VariableDeclaration,
    val additionalDeclaration: VariableDeclaration
) : Diagnostic(
    Severity.ERROR,
    run {
        var msg = "Variable ${additionalDeclaration.name.value} has already been declared."
        if (originalDeclaration.isReAssignable) {
            msg += " Write set ${originalDeclaration.name.value} = ... to assign a new value to a variable."
        }
        msg
    },
    additionalDeclaration.span
) {
    override fun toString(): String {
        var str = "$levelAndMessage\n"
        str += illustrateHints(
            SourceHint(originalDeclaration.span, "originally declared here", relativeOrderMatters = true),
            SourceHint(additionalDeclaration.span, "declared again here", relativeOrderMatters = true),
        )
        return str
    }
}
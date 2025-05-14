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

import compiler.ast.type.NamedTypeReference
import compiler.lexer.Span

class UnknownTypeDiagnostic(val erroneousReference: NamedTypeReference) : Diagnostic(
    Severity.ERROR,
    "Cannot resolve type ${erroneousReference.simpleName}",
    if (erroneousReference.declaringNameToken == null) Span.UNKNOWN else erroneousReference.declaringNameToken.span
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as UnknownTypeDiagnostic

        return erroneousReference == other.erroneousReference
    }

    override fun hashCode(): Int {
        return erroneousReference.hashCode()
    }
}
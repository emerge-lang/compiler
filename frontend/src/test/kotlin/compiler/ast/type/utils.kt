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

package compiler.compiler.ast.type

import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.basetype.BoundSupertypeList
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.mockk.every
import io.mockk.mockk

fun fakeType(name: String, vararg superTypes: BoundBaseTypeDefinition): BoundBaseTypeDefinition = mockk<BoundBaseTypeDefinition> {
    every { toString() } returns name
    every { visibility } returns BoundVisibility.ExportedScope(mockk(), mockk())
    every { validateAccessFrom(any()) } returns emptySet()
    every { toStringForErrorMessage() } returns "fake type $name"
    every { this@mockk.superTypes } returns mockk<BoundSupertypeList> {
        every { baseTypes } returns superTypes.toList()
    }
    every { canonicalName } returns CanonicalElementName.BaseType(
        CanonicalElementName.Package(listOf("fake")),
        name,
    )
}
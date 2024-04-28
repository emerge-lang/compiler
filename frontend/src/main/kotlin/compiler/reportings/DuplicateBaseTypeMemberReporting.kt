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

package compiler.reportings

import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.basetype.BoundBaseTypeMemberVariable

class DuplicateBaseTypeMemberReporting(
    val typeDef: BoundBaseTypeDefinition,
    val duplicates: Set<BoundBaseTypeMemberVariable>
) : Reporting(
    Level.ERROR,
    "Member ${duplicates.iterator().next().name} declared multiple times",
    typeDef.declaration.declaredAt,
) {
    override fun toString(): String {
        var txt = "$levelAndMessage\nin ${typeDef.declaration.declaredAt}\n"

        txt += illustrateSourceLocations(
            duplicates.map { it.declaration.sourceLocation },
        )

        return txt.trimEnd()
    }
}
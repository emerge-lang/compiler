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

import compiler.binding.struct.Struct
import compiler.binding.struct.StructMember

class DuplicateStructMemberReporting(
    val struct: Struct,
    val duplicates: Set<StructMember>
) : Reporting(
    Level.ERROR,
    "Struct member ${duplicates.iterator().next().name} declared multiple times",
    struct.declaration.declaredAt
) {
    override fun toString(): String {
        var txt = "($level) $message\n\nin ${struct.declaration.declaredAt}\n"

        txt += getIllustrationForHighlightedLines(
            duplicates.map { it.declaration.declaredAt },
        )

        return txt.trimEnd()
    }
}
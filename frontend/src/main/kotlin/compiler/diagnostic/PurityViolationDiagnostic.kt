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

import compiler.binding.BoundFunction
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.impurity.Impurity

data class PurityViolationDiagnostic(
    val impurity: Impurity,
    val boundary: SideEffectBoundary,
) : Diagnostic(
    Severity.ERROR,
    "${impurity.describe()} violates the purity of $boundary",
    impurity.span,
) {
    override fun toString(): String {
        val impurityHints = impurity.sourceHints
        if (impurityHints.isEmpty()) {
            return super.toString()
        }

        return "$levelAndMessage\n${illustrateHints(*impurityHints)}"
    }

    sealed class SideEffectBoundary {
        data class Function(val function: BoundFunction) : SideEffectBoundary() {
            override fun toString(): String {
                val modifier = if (BoundFunction.Purity.PURE.contains(function.purity)) "pure" else "readonly"
                val kindAndName = if (function is BoundClassConstructor) "constructor of class `${function.classDef.simpleName}`" else "function `${function.name}`"
                return "$modifier $kindAndName"
            }
        }
    }
}
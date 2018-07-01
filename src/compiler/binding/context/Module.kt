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

package compiler.binding.context

import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.struct.Struct
import compiler.reportings.Reporting

class Module(
    val name: Array<String>,
    val context: MutableCTContext,
    /** [Reporting]s generated at bind-time: double declarations, ... */
    val bindTimeReportings: Collection<Reporting> = emptySet()
) {
    init {
        context.module = this
    }

    /**
     * Delegates to semantic analysis phase 1 of all components that make up this module;
     * collects the results and returns them. Also returns the [Reporting]s found when binding
     * elements to the module (such as doubly declared variables).
     */
    fun semanticAnalysisPhase1(): Collection<Reporting> =
        bindTimeReportings +
        context.variables.flatMap(BoundVariable::semanticAnalysisPhase1) +
        context.functions.flatMap(BoundFunction::semanticAnalysisPhase1) +
        context.structs.flatMap(Struct::semanticAnalysisPhase1)

    /**
     * Delegates to semantic analysis phase 2 of all components that make up this module;
     * collects the results and returns them.
     */
    fun semanticAnalysisPhase2(): Collection<Reporting> =
        context.variables.flatMap(BoundVariable::semanticAnalysisPhase2) +
        context.functions.flatMap(BoundFunction::semanticAnalysisPhase2) +
        context.structs.flatMap(Struct::semanticAnalysisPhase2)

    /**
     * Delegates to semantic analysis phase 3 of all components that make up this module;
     * collects the results and returns them.
     */
    fun semanticAnalysisPhase3(): Collection<Reporting> =
        context.variables.flatMap(BoundVariable::semanticAnalysisPhase3) +
        context.functions.flatMap(BoundFunction::semanticAnalysisPhase3) +
        context.structs.flatMap(Struct::semanticAnalysisPhase3)
}
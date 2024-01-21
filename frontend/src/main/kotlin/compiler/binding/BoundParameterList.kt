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

package compiler.binding

import compiler.ast.ParameterList
import compiler.binding.context.CTContext
import compiler.reportings.Reporting

class BoundParameterList(
    val context: CTContext,
    val declaration: ParameterList,
    val parameters: List<BoundParameter>
) {
    val declaredReceiver: BoundParameter?
        get() = parameters.firstOrNull()?.takeIf { it.name == RECEIVER_PARAMETER_NAME }

    fun semanticAnalysisPhase1(allowUntypedReceiver: Boolean = false): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        parameters.forEachIndexed { index, parameter ->
            // double names
            if (index > 0) {
                val previousWithSameName = parameters.subList(0, index).find { it !== parameter && it.name == parameter.name }
                if (previousWithSameName != null) {
                    reportings.add(Reporting.parameterDeclaredMoreThanOnce(previousWithSameName.declaration, parameter.declaration))
                }
            }

            val allowUntyped = allowUntypedReceiver && index == 0 && parameter.name == RECEIVER_PARAMETER_NAME
            if (!allowUntyped && parameter.declaration.type == null) {
                reportings.add(Reporting.parameterTypeNotDeclared(parameter.declaration))
            }

            // etc.
            reportings.addAll(parameter.semanticAnalysisPhase1())
        }

        return reportings
    }

    companion object {
        const val RECEIVER_PARAMETER_NAME = "self"
    }
}

typealias BoundParameter = BoundVariable
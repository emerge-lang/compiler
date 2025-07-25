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
import compiler.ast.VariableOwnership
import compiler.binding.context.ExecutionScopedCTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.parameterDeclaredMoreThanOnce

class BoundParameterList(
    val context: ExecutionScopedCTContext,
    val declaration: ParameterList,
    val parameters: List<BoundParameter>
) {
    val declaredReceiver: BoundParameter? = parameters.firstOrNull()?.takeIf { it.name == RECEIVER_PARAMETER_NAME }
    init {
        declaredReceiver?.defaultOwnership = VariableOwnership.BORROWED
    }
    
    val modifiedContext: ExecutionScopedCTContext = parameters.lastOrNull()?.modifiedContext ?: context

    fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        parameters.forEachIndexed { index, parameter ->
            // double names
            if (index > 0) {
                val previousWithSameName = parameters.subList(0, index).find { it !== parameter && it.name == parameter.name }
                if (previousWithSameName != null) {
                    diagnosis.parameterDeclaredMoreThanOnce(previousWithSameName.declaration, parameter.declaration)
                }
            }

            parameter.semanticAnalysisPhase1(diagnosis)
        }
    }

    fun map(newOriginContext: ExecutionScopedCTContext, mapper: (parameter: BoundParameter, isReceiver: Boolean, contextCarry: ExecutionScopedCTContext) -> BoundParameter): BoundParameterList {
        val newParameters = ArrayList<BoundParameter>(parameters.size)
        for (parameter in parameters) {
            val newParameter = mapper(parameter, parameter === declaredReceiver, newOriginContext)
            newParameters.add(newParameter)
        }

        return BoundParameterList(
            newOriginContext,
            ParameterList(newParameters.map { it.declaration }),
            newParameters,
        )
    }

    companion object {
        const val RECEIVER_PARAMETER_NAME = "self"
    }
}

typealias BoundParameter = BoundVariable
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

import compiler.ast.type.TypeReference
import compiler.binding.BoundParameter
import compiler.binding.BoundParameterList
import compiler.binding.BoundVariable
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.RootResolvedTypeReference

data class ParameterList (
    val parameters: List<VariableDeclaration> = emptyList()
) {
    /** The types; null values indicate non-specified parameters */
    val types: List<TypeReference?> = parameters.map { it.type }

    fun bindTo(context: ExecutionScopedCTContext, lazyImpliedReceiverType: (() -> RootResolvedTypeReference)? = null): BoundParameterList {
        val boundParams = mutableListOf<BoundParameter>()
        var contextCarry = context
        for ((index, parameter) in parameters.withIndex()) {
            val bound = parameter.bindToAsParameter(
                contextCarry,
                if (index == 0 && parameter.name.value == BoundParameterList.RECEIVER_PARAMETER_NAME && lazyImpliedReceiverType != null) {
                    BoundVariable.TypeInferenceStrategy.ImpliedTypeIgnoreInitializer(lazyImpliedReceiverType)
                } else {
                    BoundVariable.TypeInferenceStrategy.NoInference
                }
            )
            contextCarry = bound.modifiedContext
            boundParams.add(bound)
        }

        return BoundParameterList(context, this, boundParams)
    }
}
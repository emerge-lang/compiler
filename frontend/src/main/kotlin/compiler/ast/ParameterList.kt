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

import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeReference
import compiler.binding.BoundParameterList
import compiler.binding.context.ExecutionScopedCTContext

data class ParameterList (
    val parameters: List<VariableDeclaration> = emptyList()
) {
    /** The types; null values indicate non-specified parameters */
    val types: List<TypeReference?> = parameters.map { it.type }

    fun bindTo(context: ExecutionScopedCTContext, impliedReceiverType: NamedTypeReference? = null) = BoundParameterList(
        context,
        this,
        parameters.mapIndexed { index, parameter ->
            if (index == 0 && parameter.name.value == BoundParameterList.RECEIVER_PARAMETER_NAME ) {
                val actualType = when {
                    parameter.type != null && impliedReceiverType != null -> parameter.type.fillInInferrableType(impliedReceiverType)
                    else -> parameter.type ?: impliedReceiverType
                }

                val retypedParam = if (actualType === parameter.type) parameter else parameter.copy(type = actualType)
                return@mapIndexed retypedParam.bindToAsParameter(context)
            }

            return@mapIndexed parameter.bindToAsParameter(context)
        },
    )
}
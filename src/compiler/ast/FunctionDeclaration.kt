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

import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundParameterList
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

class FunctionDeclaration(
    override val declaredAt: SourceLocation,
    val modifiers: Set<FunctionModifier>,
    val name: IdentifierToken,
    val typeParameters: List<TypeParameter>,
    val parameters: ParameterList,
    parsedReturnType: TypeReference?,
    val code: Executable<*>?,
) : Declaration, Bindable<BoundDeclaredFunction> {

    /**
     * The return type. Is null if none was declared and it has not been inferred yet (see semantic analysis phase 2)
     */
    val returnType: TypeReference? = parsedReturnType

    override fun bindTo(context: CTContext): BoundDeclaredFunction {
        val functionContext = MutableCTContext(context)
        val boundTypeParams = typeParameters.map(functionContext::addTypeParameter)

        val boundParams = parameters.parameters.map {
            val bound = it.bindToAsParameter(functionContext)
            functionContext.addVariable(bound)
            bound
        }
        val boundParamList = BoundParameterList(context, parameters, boundParams)

        return BoundDeclaredFunction(
            functionContext,
            this,
            boundTypeParams,
            boundParamList,
            code?.bindTo(functionContext)
        )
    }
}

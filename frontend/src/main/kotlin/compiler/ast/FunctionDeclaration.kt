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

import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundTopLevelFunction
import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.basetype.BoundDeclaredBaseTypeMemberFunction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter.Companion.chain
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken

data class FunctionDeclaration(
    val declarationKeyword: KeywordToken,
    val attributes: List<AstFunctionAttribute>,
    val name: IdentifierToken,
    val typeParameters: List<TypeParameter>,
    val parameters: ParameterList,
    val parsedReturnType: TypeReference?,
    val body: Body?,
) : AstFileLevelDeclaration {
    override val declaredAt = name.sourceLocation

    fun bindToAsTopLevel(context: CTContext): BoundTopLevelFunction {
        val (boundTypeParams, contextWithTypeParams) = typeParameters.chain(context)
        val functionContext = MutableExecutionScopedCTContext.functionRootIn(contextWithTypeParams)
        val attributes = BoundFunctionAttributeList(functionContext, attributes)
        val boundParameterList = parameters.bindTo(functionContext)

        return BoundTopLevelFunction(
            functionContext,
            this,
            attributes,
            boundTypeParams,
            boundParameterList,
            body?.bindTo(boundParameterList.modifiedContext),
        )
    }

    fun bindToAsMember(
        context: CTContext,
        impliedReceiverType: TypeReference,
        getTypeDef: () -> BoundBaseTypeDefinition
    ): BoundDeclaredBaseTypeMemberFunction {
        val (boundTypeParams, contextWithTypeParams) = typeParameters.chain(context)
        val functionContext = MutableExecutionScopedCTContext.functionRootIn(contextWithTypeParams)
        val attributes = BoundFunctionAttributeList(functionContext, attributes)
        val boundParameterList = parameters.bindTo(functionContext, impliedReceiverType)

        return BoundDeclaredBaseTypeMemberFunction(
            functionContext,
            this,
            attributes,
            boundTypeParams,
            boundParameterList,
            body?.bindTo(boundParameterList.modifiedContext),
            getTypeDef,
        )
    }

    sealed interface Body {
        fun bindTo(context: ExecutionScopedCTContext): BoundDeclaredFunction.Body

        class SingleExpression(val expression: Expression) : Body {
            override fun bindTo(context: ExecutionScopedCTContext): BoundDeclaredFunction.Body {
                return BoundDeclaredFunction.Body.SingleExpression(
                    expression.bindTo(context)
                )
            }
        }

        class Full(val code: CodeChunk) : Body {
            override fun bindTo(context: ExecutionScopedCTContext): BoundDeclaredFunction.Body {
                return BoundDeclaredFunction.Body.Full(code.bindTo(context))
            }
        }
    }
}

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
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.context.ExecutionScopedCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken
import compiler.lexer.Span

data class VariableDeclaration(
    override val declaredAt: Span,
    val visibility: AstVisibility?,
    val varToken: KeywordToken?,
    val ownership: Pair<VariableOwnership, KeywordToken>?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val initializerExpression: Expression?
) : Statement, AstFileLevelDeclaration {
    override val span get() = declaredAt
    val isReAssignable: Boolean = varToken != null

    override fun bindTo(context: ExecutionScopedCTContext): BoundVariable = bindToAsLocalVariable(context)

    fun bindToAsGlobalVariable(context: ExecutionScopedCTContext, initializerContext: ExecutionScopedCTContext): BoundVariable {
        return bindTo(context, initializerContext, BoundVariable.TypeInferenceStrategy.InferBaseTypeAndMutability, BoundVariable.Kind.GLOBAL_VARIABLE)
    }

    fun bindToAsParameter(
        context: ExecutionScopedCTContext,
        typeInferenceStrategy: BoundVariable.TypeInferenceStrategy
    ): BoundVariable {
        return bindTo(context, context, typeInferenceStrategy, BoundVariable.Kind.PARAMETER)
    }

    fun bindToAsConstructorParameter(context: ExecutionScopedCTContext): BoundVariable {
        return bindTo(context, context, BoundVariable.TypeInferenceStrategy.NoInference, BoundVariable.Kind.CONSTRUCTOR_PARAMETER)
    }

    fun bindToAsLocalVariable(context: ExecutionScopedCTContext): BoundVariable {
        return bindTo(context, context, BoundVariable.TypeInferenceStrategy.InferBaseTypeAndMutability, BoundVariable.Kind.LOCAL_VARIABLE)
    }

    fun bindToAsMemberVariable(context: ExecutionScopedCTContext, isDecorated: Boolean): BoundVariable {
        return bindTo(
            context,
            context,
            BoundVariable.TypeInferenceStrategy.InferBaseTypeAndMutability,
            if (isDecorated) BoundVariable.Kind.DECORATED_MEMBER_VARIABLE else BoundVariable.Kind.MEMBER_VARIABLE,
        )
    }

    private fun bindTo(
        context: ExecutionScopedCTContext,
        initializerContext: ExecutionScopedCTContext,
        typeInferenceStrategy: BoundVariable.TypeInferenceStrategy,
        kind: BoundVariable.Kind
    ): BoundVariable {
        return BoundVariable(
            context,
            this,
            visibility?.bindTo(context) ?: BoundVisibility.default(context),
            initializerExpression?.bindTo(initializerContext),
            typeInferenceStrategy,
            kind,
        )
    }
}
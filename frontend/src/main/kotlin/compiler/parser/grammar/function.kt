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

package compiler.parser.grammar

import compiler.InternalCompilerError
import compiler.ast.*
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.sequence
import java.util.*
import compiler.ast.Expression as AstExpression

val Parameter = sequence("parameter declaration") {
    optional {
        ref(VariableOwnership)
    }
    optional {
        keyword(Keyword.VAR)
    }
    ref(Identifier)
    optional {
        operator(Operator.COLON)
        ref(Type)
    }
    optional {
        operator(Operator.ASSIGNMENT)
        ref(Expression)
    }
}
    .astTransformation { tokens ->
        var next: Any? = tokens.next()!!

        val varKeywordToken: KeywordToken?
        val ownership: Pair<VariableOwnership, KeywordToken>?
        if (next is Pair<*, *>) {
            @Suppress("UNCHECKED_CAST")
            ownership = next as Pair<VariableOwnership, KeywordToken>
            next = tokens.next()!!
        } else {
            ownership = null
        }

        if (next is KeywordToken) {
            varKeywordToken = next
            next = tokens.next()!!
        } else {
            varKeywordToken = null
        }
        val name = next as IdentifierToken
        next = tokens.next() as OperatorToken?

        var type: TypeReference?
        if (next != null && next.operator == Operator.COLON) {
            type = tokens.next() as TypeReference
            next = tokens.next()
        } else {
            type = null
        }

        val defaultValue: AstExpression? = if (next != null) {
            tokens.next() as AstExpression
        } else {
            null
        }

        VariableDeclaration(
            name.span,
            null,
            varKeywordToken,
            ownership,
            name,
            type,
            defaultValue,
        )
    }

val ParameterList = sequence("parenthesised parameter list") {
    operator(Operator.PARANT_OPEN)

    optional {
        ref(Parameter)
        repeating {
            operator(Operator.COMMA)
            ref(Parameter)
        }
    }

    optional {
        operator(Operator.COMMA)
    }
    operator(Operator.PARANT_CLOSE)
}
    .astTransformation { tokens ->
        // skip PARANT_OPEN
        tokens.next()!!

        val parameters: MutableList<VariableDeclaration> = LinkedList()

        while (tokens.hasNext()) {
            var next = tokens.next()!!
            if (next == OperatorToken(Operator.PARANT_CLOSE)) {
                return@astTransformation ParameterList(parameters)
            }

            parameters.add(next as VariableDeclaration)

            tokens.mark()

            next = tokens.next()!!
            if (next == OperatorToken(Operator.PARANT_CLOSE)) {
                tokens.commit()
                return@astTransformation ParameterList(parameters)
            }

            if (next == OperatorToken(Operator.COMMA)) {
                tokens.commit()
            }
            else if (next !is VariableDeclaration) {
                tokens.rollback()
                next as Token
                throw InternalCompilerError("Unexpected ${next.toStringWithoutLocation()} in parameter list, expecting ${Operator.PARANT_CLOSE.text} or ${Operator.COMMA.text}")
            }
        }

        throw InternalCompilerError("This line should never have been reached :(")
    }

val FunctionAttribute = eitherOf {
    keyword(Keyword.MUTABLE)
    keyword(Keyword.READONLY)
    keyword(Keyword.PURE)
    keyword(Keyword.NOTHROW)
    keyword(Keyword.OPERATOR)
    keyword(Keyword.INTRINSIC)
    keyword(Keyword.OVERRIDE)
    sequence {
        keyword(Keyword.EXTERNAL)
        operator(Operator.PARANT_OPEN)
        ref(Identifier)
        operator(Operator.PARANT_CLOSE)
    }
    ref(Visibility)
}
    .astTransformation { tokens ->
        val next = tokens.next()
        if (next is AstVisibility) {
            return@astTransformation next
        }
        val nameToken = next as KeywordToken
        when(nameToken.keyword) {
            Keyword.MUTABLE -> AstFunctionAttribute.EffectCategory(AstFunctionAttribute.EffectCategory.Category.MODIFYING, nameToken)
            Keyword.READONLY -> AstFunctionAttribute.EffectCategory(AstFunctionAttribute.EffectCategory.Category.READONLY, nameToken)
            Keyword.PURE -> AstFunctionAttribute.EffectCategory(AstFunctionAttribute.EffectCategory.Category.PURE, nameToken)
            Keyword.NOTHROW -> AstFunctionAttribute.Nothrow(nameToken)
            Keyword.OPERATOR -> AstFunctionAttribute.Operator(nameToken)
            Keyword.INTRINSIC -> AstFunctionAttribute.Intrinsic(nameToken)
            Keyword.OVERRIDE -> AstFunctionAttribute.Override(nameToken)
            Keyword.EXTERNAL -> {
                tokens.next() // skip parant_open
                val ffiNameToken = tokens.next() as IdentifierToken

                AstFunctionAttribute.External(nameToken, ffiNameToken)
            }
            else -> throw InternalCompilerError("grammar mismatch with ast transform")
        }
    }

val FunctionAttributes = sequence("function attributes") {
    repeating {
        ref(FunctionAttribute)
    }
}
    .astTransformation { tokens ->
        tokens.remainingToList().map { it as AstFunctionAttribute }
    }

val StandaloneFunctionDeclaration = sequence("function declaration") {
    ref(FunctionAttributes)
    keyword(Keyword.FUNCTION)
    ref(Identifier)
    optional {
        ref(BracedTypeParameters)
    }
    ref(ParameterList)

    optional {
        operator(Operator.RETURNS)
        ref(Type)
    }

    eitherOf {
        sequence {
            operator(Operator.CBRACE_OPEN)
            ref(CodeChunk)
            operator(Operator.CBRACE_CLOSE)
        }
        sequence {
            operator(Operator.ASSIGNMENT)
            ref(Expression)
            operator(Operator.NEWLINE)
        }
        operator(Operator.NEWLINE)
    }
}
    .astTransformation { tokens ->
        val attributes = tokens.next() as List<AstFunctionAttribute>
        val declarationKeyword = tokens.next() as KeywordToken
        val name = tokens.next() as IdentifierToken

        var next: Any? = tokens.next()!!
        val typeParameters: List<TypeParameter>
        if (next is TypeParameterBundle) {
            typeParameters = next.parameters
            next = tokens.next()!!
        } else {
            typeParameters = emptyList()
        }

        val parameterList = next as ParameterList

        next = tokens.next()

        var type: TypeReference? = null

        if (next == OperatorToken(Operator.RETURNS)) {
            type = tokens.next()!! as TypeReference
            next = tokens.next()
        }

        if (next == OperatorToken(Operator.CBRACE_OPEN)) {
            val code = tokens.next()!! as AstCodeChunk
            // ignore trailing CBRACE_CLOSE

            return@astTransformation FunctionDeclaration(
                declarationKeyword,
                attributes,
                name,
                typeParameters,
                parameterList,
                type ?: TypeReference("Unit", nullability = TypeReference.Nullability.UNSPECIFIED),
                FunctionDeclaration.Body.Full(code),
            )
        }

        if (next == OperatorToken(Operator.ASSIGNMENT)) {
            val singleExpression = tokens.next()!! as AstExpression

            return@astTransformation FunctionDeclaration(
                declarationKeyword,
                attributes,
                name,
                typeParameters,
                parameterList,
                type,
                FunctionDeclaration.Body.SingleExpression(singleExpression),
            )
        }

        if (next == OperatorToken(Operator.NEWLINE) || next == null) {
            // function without body with trailing newline or immediately followed by EOF
            return@astTransformation FunctionDeclaration(
                declarationKeyword,
                attributes,
                name,
                typeParameters,
                parameterList,
                type,
                null
            )
        }

        throw InternalCompilerError("Unexpected token when building AST: expected ${OperatorToken(Operator.CBRACE_OPEN)} or ${OperatorToken(Operator.ASSIGNMENT)} but got $next")
    }

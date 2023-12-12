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
import compiler.ast.CodeChunk
import compiler.ast.FunctionDeclaration
import compiler.ast.ParameterList
import compiler.ast.TypeParameterBundle
import compiler.ast.VariableDeclaration
import compiler.ast.expression.Expression
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Token
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.sequence
import java.util.LinkedList

val Parameter = sequence("parameter declaration") {

    optional {
        ref(TypeMutability)
    }

    optional {
        eitherOf {
            keyword(Keyword.VAR)
            keyword(Keyword.VAL)
        }
    }

    identifier()

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
        var declarationKeyword: Keyword? = null
        var typeMutability: TypeMutability? = null
        val name: IdentifierToken
        var type: TypeReference? = null
        var initializer: Expression<*>? = null

        var next = tokens.next()!!

        if (next is KeywordToken) {
            declarationKeyword = next.keyword
            next = tokens.next()!!
        }

        if (next is TypeMutability) {
            typeMutability = next
            next = tokens.next()!!
        }

        name = next as IdentifierToken

        if (tokens.peek() == OperatorToken(Operator.COLON)) {
            tokens.next()
            type = tokens.next()!! as TypeReference
        }

        if (tokens.peek() == OperatorToken(Operator.ASSIGNMENT)) {
            tokens.next()
            initializer = tokens.next()!! as Expression<*>
        }

        VariableDeclaration(
            name.sourceLocation,
            typeMutability,
            name,
            type,
            declarationKeyword == Keyword.VAR,
            initializer,
        )
    }

val ParameterList = sequence("parenthesised parameter list") {
    operator(Operator.PARANT_OPEN)

    optionalWhitespace()

    optional {
        ref(Parameter)

        optionalWhitespace()

        repeating {
            operator(Operator.COMMA)
            optionalWhitespace()
            ref(Parameter)
        }
    }

    optionalWhitespace()
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

val FunctionModifier = sequence {
    eitherOf {
        keyword(Keyword.READONLY)
        keyword(Keyword.NOTHROW)
        keyword(Keyword.PURE)
        keyword(Keyword.OPERATOR)
        keyword(Keyword.EXTERNAL)
    }
}
    .astTransformation { tokens -> when((tokens.next()!! as KeywordToken).keyword) {
        Keyword.READONLY -> compiler.ast.type.FunctionModifier.READONLY
        Keyword.NOTHROW  -> compiler.ast.type.FunctionModifier.NOTHROW
        Keyword.PURE     -> compiler.ast.type.FunctionModifier.PURE
        Keyword.OPERATOR -> compiler.ast.type.FunctionModifier.OPERATOR
        Keyword.EXTERNAL -> compiler.ast.type.FunctionModifier.EXTERNAL
        else             -> throw InternalCompilerError("Keyword is not a function modifier")
    } }

val StandaloneFunctionDeclaration = sequence("function declaration") {
    repeating {
        ref(FunctionModifier)
    }

    keyword(Keyword.FUNCTION)

    optional {
        ref(Type)
        operator(Operator.DOT)
    }

    optionalWhitespace()
    identifier()
    optionalWhitespace()
    optional {
        ref(BracedTypeParameters)
    }
    optionalWhitespace()
    ref(ParameterList)
    optionalWhitespace()

    optional {
        operator(Operator.RETURNS)
        optionalWhitespace()
        ref(Type)
    }

    eitherOf {
        sequence {
            optionalWhitespace()
            operator(Operator.CBRACE_OPEN)
            ref(CodeChunk)
            optionalWhitespace()
            operator(Operator.CBRACE_CLOSE)
        }
        sequence {
            operator(Operator.ASSIGNMENT)
            ref(Expression)
            eitherOf {
                operator(Operator.NEWLINE)
                endOfInput()
            }
        }
        operator(Operator.NEWLINE)
        endOfInput()
    }
}
    .astTransformation { tokens ->
        val modifiers = mutableSetOf<FunctionModifier>()
        var next: Any? = tokens.next()!!
        while (next is FunctionModifier) {
            modifiers.add(next)
            next = tokens.next()!!
        }

        val declarationKeyword = next as KeywordToken

        val receiverType: TypeReference?
        next = tokens.next()!!
        if (next is TypeReference) {
            receiverType = next
            // skip DOT
            tokens.next()

            next = tokens.next()!!
        }
        else {
            receiverType = null
        }

        val name = next as IdentifierToken

        next = tokens.next()!!
        val typeParameters: List<TypeParameter>
        if (next is TypeParameterBundle) {
            typeParameters = next.parameters
            next = tokens.next()!!
        } else {
            typeParameters = emptyList()
        }

        val parameterList = next as ParameterList

        next = tokens.next()!!

        var type: TypeReference? = null

        if (next == OperatorToken(Operator.RETURNS)) {
            type = tokens.next()!! as TypeReference
            next = tokens.next()
        }

        if (next == OperatorToken(Operator.CBRACE_OPEN)) {
            val code = tokens.next()!! as CodeChunk
            // ignore trailing CBRACE_CLOSE

            return@astTransformation FunctionDeclaration(
                declarationKeyword.sourceLocation,
                modifiers,
                receiverType,
                name,
                typeParameters,
                parameterList,
                type ?: TypeReference("Unit", nullability = TypeReference.Nullability.UNSPECIFIED),
                code
            )
        }

        if (next == OperatorToken(Operator.ASSIGNMENT)) {
            val singleExpression = tokens.next()!! as Expression<*>

            return@astTransformation FunctionDeclaration(
                declarationKeyword.sourceLocation,
                modifiers,
                receiverType,
                name,
                typeParameters,
                parameterList,
                type,
                singleExpression,
            )
        }

        if (next == OperatorToken(Operator.NEWLINE) || next == null) {
            // function without body with trailing newline or immediately followed by EOF
            return@astTransformation FunctionDeclaration(
                declarationKeyword.sourceLocation,
                modifiers,
                receiverType,
                name,
                typeParameters,
                parameterList,
                type,
                null
            )
        }

        throw InternalCompilerError("Unexpected token when building AST: expected ${OperatorToken(Operator.CBRACE_OPEN)} or ${OperatorToken(Operator.ASSIGNMENT)} but got $next")
    }

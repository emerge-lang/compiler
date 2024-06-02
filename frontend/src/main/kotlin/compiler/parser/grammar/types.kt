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
import compiler.ast.TypeArgumentBundle
import compiler.ast.TypeParameterBundle
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.isolateCyclicGrammar
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.Rule

val TypeMutability = eitherOf("type mutability") {
    keyword(Keyword.MUTABLE)
    keyword(Keyword.READONLY)
    keyword(Keyword.IMMUTABLE)
    keyword(Keyword.EXCLUSIVE)
}
    .mapResult { keywordToken ->
        keywordToken as KeywordToken
        when(keywordToken.keyword) {
            Keyword.MUTABLE   -> compiler.ast.type.TypeMutability.MUTABLE
            Keyword.READONLY  -> compiler.ast.type.TypeMutability.READONLY
            Keyword.IMMUTABLE -> compiler.ast.type.TypeMutability.IMMUTABLE
            Keyword.EXCLUSIVE -> compiler.ast.type.TypeMutability.EXCLUSIVE
            else -> throw InternalCompilerError("${keywordToken.keyword} is not a type modifier")
        }
    }

private val TypeArgument = sequence {
    ref(Variance)
    ref(Type)
}
    .astTransformation { tokens ->
        val variance = tokens.next() as TypeVariance
        val type = tokens.next() as TypeReference
        TypeArgument(variance, type)
    }

val BracedTypeArguments: Rule<TypeArgumentBundle> = sequence {
    operator(Operator.LESS_THAN)
    optional {
        ref(TypeArgument)
        repeating {
            operator(Operator.COMMA)
            ref(TypeArgument)
        }
    }
    operator(Operator.GREATER_THAN)
}
    .astTransformation { tokens ->
        // skip <
        tokens.next()

        val arguments = ArrayList<TypeArgument>()
        while (tokens.hasNext()) {
            arguments.add(tokens.next() as TypeArgument)
            // skip , or >
            tokens.next()
        }

        TypeArgumentBundle(arguments)
    }

val Variance: Rule<TypeVariance> = sequence("variance") {
    optional {
        eitherOf {
            keyword(Keyword.VARIANCE_IN)
            keyword(Keyword.VARIANCE_OUT)
        }
    }
}
    .astTransformation { tokens ->
        when (val keyword = (tokens.next() as KeywordToken?)?.keyword) {
            null -> TypeVariance.UNSPECIFIED
            Keyword.VARIANCE_IN -> TypeVariance.IN
            Keyword.VARIANCE_OUT -> TypeVariance.OUT
            else -> throw InternalCompilerError("$keyword is not a type variance")
        }
    }

val TypeParameter = sequence("type parameter") {
    ref(Variance)
    ref(Identifier)
    optional {
        operator(Operator.COLON)
        ref(Type)
    }
}
    .astTransformation { tokens ->
        val variance = tokens.next() as TypeVariance
        val name = tokens.next() as IdentifierToken
        val bound = if (tokens.hasNext()) {
            tokens.next() // skip colon
            tokens.next() as TypeReference
        } else null

        TypeParameter(variance, name, bound)
    }

val BracedTypeParameters = sequence("braced type parameters") {
    operator(Operator.LESS_THAN)
    optional {
        ref(TypeParameter)
        repeating {
            operator(Operator.COMMA)
            ref(TypeParameter)
        }
    }
    operator(Operator.GREATER_THAN)
}
    .astTransformation { tokens ->
        // skip <
        tokens.next()

        val parameters = ArrayList<TypeParameter>()
        while (tokens.hasNext()) {
            parameters.add(tokens.next() as TypeParameter)
            // skip , or >
            tokens.next()
        }

        TypeParameterBundle(parameters)
    }

val Type: Rule<TypeReference> = sequence("type") {
    optional {
        ref(TypeMutability)
    }

    ref(Identifier)

    optional {
        ref(BracedTypeArguments)
    }

    optional {
        eitherOf(Operator.QUESTION_MARK, Operator.EXCLAMATION_MARK)
    }

    // TODO: function types
}
    .isolateCyclicGrammar
    .astTransformation { tokens ->
        val nameOrModifier = tokens.next()!!

        val typeMutability: TypeMutability?
        val nameToken: IdentifierToken

        if (nameOrModifier is TypeMutability) {
            typeMutability = nameOrModifier
            nameToken = tokens.next()!! as IdentifierToken
        }
        else {
            typeMutability = null
            nameToken = nameOrModifier as IdentifierToken
        }

        var next = tokens.next()
        val arguments: List<TypeArgument>?
        if (next is TypeArgumentBundle) {
            arguments = next.arguments
            next = tokens.next()
        } else {
            arguments = null
        }

        val nullability = when (next) {
            null -> TypeReference.Nullability.UNSPECIFIED
            is OperatorToken -> when(next.operator) {
                Operator.QUESTION_MARK -> TypeReference.Nullability.NULLABLE
                Operator.NOTNULL -> TypeReference.Nullability.NOT_NULLABLE
                else -> throw InternalCompilerError("Unknown type nullability marker: $next")
            }
            else -> throw InternalCompilerError("Unknown type nullability marker: $next")
        }

        TypeReference(
            nameToken.value,
            nullability,
            typeMutability,
            nameToken,
            arguments,
        )
    }


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
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
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

val TypeModifier = eitherOf("type modifier") {
    keyword(Keyword.MUTABLE)
    keyword(Keyword.READONLY)
    keyword(Keyword.IMMUTABLE)
}
    .mapResult { keywordToken ->
        keywordToken as KeywordToken
        when(keywordToken.keyword) {
            Keyword.MUTABLE   -> compiler.ast.type.TypeModifier.MUTABLE
            Keyword.READONLY  -> compiler.ast.type.TypeModifier.READONLY
            Keyword.IMMUTABLE -> compiler.ast.type.TypeModifier.IMMUTABLE
            else -> throw InternalCompilerError("${keywordToken.keyword} is not a type modifier")
        }
    }

private val ReferencingTypeParameter = sequence {
    optional {
        eitherOf {
            keyword(Keyword.VARIANCE_IN)
            keyword(Keyword.VARIANCE_OUT)
        }
    }
    ref(Type)
}
    .astTransformation { tokens ->
        val firstToken = tokens.next()
        val variance: TypeReference.Variance
        val typeReference: TypeReference

        when (firstToken) {
            is TypeReference -> {
                variance = TypeReference.Variance.UNSPECIFIED
                typeReference = firstToken
            }
            is KeywordToken -> {
                variance = when(firstToken.keyword) {
                    Keyword.VARIANCE_IN -> TypeReference.Variance.IN
                    Keyword.VARIANCE_OUT -> TypeReference.Variance.OUT
                    else -> throw InternalCompilerError("Unknown type variance $firstToken")
                }
                typeReference = tokens.next() as TypeReference
            }
            else -> throw InternalCompilerError("Unexpected token in referencing type parameter: $firstToken")
        }

        typeReference.withVariance(variance)
    }

private val ReferencingTypeParameters: Rule<TypeReferenceParameters> = sequence {
    operator(Operator.LESS_THAN)
    optional {
        ref(ReferencingTypeParameter)
        repeating {
            operator(Operator.COMMA)
            ref(ReferencingTypeParameter)
        }
    }
    operator(Operator.GREATER_THAN)
}
    .astTransformation { tokens ->
        // skip <
        tokens.next()

        val parameters = ArrayList<TypeReference>()
        while (tokens.hasNext()) {
            parameters.add(tokens.next() as TypeReference)
            // skip , or >
            tokens.next()
        }

        TypeReferenceParameters(parameters)
    }

val DeclaringTypeParameter = sequence {
    ref(ReferencingTypeParameter)
    optional {
        operator(Operator.COLON)
        ref(Type)
    }
}
    .astTransformation { tokens ->
        val type = tokens.next() as TypeReference
        val bound = if (tokens.hasNext()) {
            // skip :
            tokens.next()
            tokens.next() as TypeReference
        } else null

        TypeParameter(type, bound)
    }

val Type: Rule<TypeReference> = sequence("type") {
    optional {
        ref(TypeModifier)
    }

    identifier()

    optional {
        ref(ReferencingTypeParameters)
    }

    optional {
        eitherOf(Operator.QUESTION_MARK, Operator.NOTNULL)
    }

    // TODO: function types
}
    .isolateCyclicGrammar
    .astTransformation { tokens ->
        val nameOrModifier = tokens.next()!!

        val typeModifier: TypeModifier?
        val nameToken: IdentifierToken

        if (nameOrModifier is TypeModifier) {
            typeModifier = nameOrModifier
            nameToken = tokens.next()!! as IdentifierToken
        }
        else {
            typeModifier = null
            nameToken = nameOrModifier as IdentifierToken
        }

        var next = tokens.next()
        val parameters: List<TypeReference>
        if (next is TypeReferenceParameters) {
            parameters = next.parameters
            next = tokens.next()
        } else {
            parameters = emptyList()
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
            typeModifier,
            TypeReference.Variance.UNSPECIFIED,
            nameToken,
            parameters,
        )
    }

// needed because a bare List<*> doesn't survive the flatten()
private class TypeReferenceParameters(val parameters: List<TypeReference>)
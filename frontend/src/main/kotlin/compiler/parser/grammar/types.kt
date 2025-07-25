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
import compiler.ast.type.AstIntersectionType
import compiler.ast.type.AstSpecificTypeArgument
import compiler.ast.type.AstTypeArgument
import compiler.ast.type.AstWildcardTypeArgument
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Span
import compiler.parser.AstIntersectionTypePostfix
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.Rule

val TypeMutability = eitherOf("type mutability") {
    keyword(Keyword.MUTABLE)
    keyword(Keyword.READONLY)
    keyword(Keyword.IMMUTABLE)
    keyword(Keyword.EXCLUSIVE)
}

private val TypeArgument = sequence {
    ref(Variance)
    eitherOf {
        ref(Type)
        operator(Operator.TIMES)
    }
}
    .astTransformation { tokens ->
        val variance = tokens.next() as TypeVariance
        val next = tokens.next()
        if (next is TypeReference) {
            AstSpecificTypeArgument(variance, next)
        } else {
            AstWildcardTypeArgument(variance, (next as OperatorToken).span)
        }
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

        val arguments = ArrayList<AstTypeArgument>()
        while (tokens.hasNext()) {
            arguments.add(tokens.next() as AstTypeArgument)
            // skip , or >
            tokens.next()
        }

        TypeArgumentBundle(arguments)
    }

val Variance: Rule<TypeVariance> = sequence("variance") {
    optional {
        eitherOf {
            keyword(Keyword.IN)
            keyword(Keyword.VARIANCE_OUT)
        }
    }
}
    .astTransformation { tokens ->
        when (val keyword = (tokens.next() as KeywordToken?)?.keyword) {
            null -> TypeVariance.UNSPECIFIED
            Keyword.IN -> TypeVariance.IN
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

val NamedType: Rule<TypeReference> = sequence("named type") {
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
    .astTransformation { tokens ->
        val nameOrMutability = tokens.next()!!

        val typeMutabilityKeyword: KeywordToken?
        val nameToken: IdentifierToken

        if (nameOrMutability is KeywordToken) {
            typeMutabilityKeyword = nameOrMutability
            nameToken = tokens.next()!! as IdentifierToken
        }
        else {
            typeMutabilityKeyword = null
            nameToken = nameOrMutability as IdentifierToken
        }

        var next = tokens.next()
        val arguments: List<AstTypeArgument>?
        if (next is TypeArgumentBundle) {
            arguments = next.arguments
            next = tokens.next()
        } else {
            arguments = null
        }

        val nullabilityToken: OperatorToken?
        val nullability: TypeReference.Nullability
        when (next) {
            null -> {
                nullabilityToken = null
                nullability = TypeReference.Nullability.UNSPECIFIED
            }
            is OperatorToken -> {
                nullabilityToken = next
                nullability = when(next.operator) {
                    Operator.QUESTION_MARK -> TypeReference.Nullability.NULLABLE
                    Operator.NOTNULL -> TypeReference.Nullability.NOT_NULLABLE
                    else -> throw InternalCompilerError("Unknown type nullability marker: $next")
                }
            }
            else -> throw InternalCompilerError("Unknown type nullability marker: $next")
        }

        val typeMutability = when(typeMutabilityKeyword?.keyword) {
            Keyword.MUTABLE   -> compiler.ast.type.TypeMutability.MUTABLE
            Keyword.READONLY  -> compiler.ast.type.TypeMutability.READONLY
            Keyword.IMMUTABLE -> compiler.ast.type.TypeMutability.IMMUTABLE
            Keyword.EXCLUSIVE -> compiler.ast.type.TypeMutability.EXCLUSIVE
            null -> null
            else -> throw InternalCompilerError("Invalid type mutability token: $typeMutabilityKeyword")
        }

        NamedTypeReference(
            nameToken.value,
            nullability,
            typeMutability,
            nameToken,
            arguments,
            Span.range(typeMutabilityKeyword?.span, nameToken.span, nullabilityToken?.span, *(arguments ?: emptyList()).map { it.span }.toTypedArray()),
        )
    }

val IntersectionTypePostifx = sequence("intersection-postfix") {
    operator(Operator.INTERSECTION)
    ref(NamedType)
}
    .astTransformation { tokens ->
        AstIntersectionTypePostfix(tokens.next() as OperatorToken, tokens.next() as NamedTypeReference)
    }

val Type: Rule<TypeReference> = sequence("type") {
    ref(NamedType)
    repeating {
        ref(IntersectionTypePostifx)
    }
}
    .astTransformation { tokens ->
        val baseRef = tokens.next() as NamedTypeReference
        val intersections = tokens.remainingToList() as List<AstIntersectionTypePostfix>
        if (intersections.isEmpty()) {
            return@astTransformation baseRef
        }

        var combinedSpan = intersections.fold(baseRef.span ?: Span.UNKNOWN) { carrySpan, postfix ->
            carrySpan
                .rangeTo(postfix.reference.span)
                .rangeTo(postfix.intersectionOperator.span)
        }

        AstIntersectionType(listOf(baseRef) + intersections.map { it.reference }, combinedSpan)
    }
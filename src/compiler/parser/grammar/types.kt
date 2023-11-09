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
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence

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

val Type = sequence("type") {
    optional {
        ref(TypeModifier)
    }

    identifier()
    optional {
        operator(Operator.QUESTION_MARK)
    }

    // TODO: function types
    // TODO: generics
}
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

        val isNullable = tokens.hasNext() && tokens.next()!! == OperatorToken(Operator.QUESTION_MARK)

        TypeReference(nameToken, isNullable, typeModifier)
    }